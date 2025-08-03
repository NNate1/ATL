// SPDX-License-Identifier: MIT
// Copyright (C) 2024 Nuno Policarpo

open ATL
/*
 * Generic DHT model
 * Operations modelled as intervals
 *
 * Membership Operations:
 * 	- Join
 * 	- Fail
 * 	- Leave
 *
 * Functional Operations:
 * 	- Store
 * 	- Lookup
 * 	- Find
 *
 *
 * Properties:
 *  - Key Consistency
 *  - Lookup Consistency
 * 	- Value Consistency
 * 	- Value Freshness
 *  - Reachability
 *  - Membership Guarantee
 *  - FindNode Lookup Consistency
 *  - Responsibility Expiration
 *  - Responsibility Transfer
 *  - Termination Completeness
*/


// Ignore library test signatures
fact {
	no T
	no P
	no Proposition
}

/*
 * Visualization functions
 */

// Starting interval
fun A_Starting : Interval {
	 ATL/Starting - Member - Responsible
}

// Ending interval
fun B_Ending : Interval {
	 ATL/Ending - Member - Responsible
}

fun C_Ongoing_Visual : Interval {
	 ATL/Ongoing-ATL/Starting - ATL/Ending - Member - Responsible
}

// Visualize Responsible Nodes
fun Visual_Responsible : Node -> Key {
	{n: Node, k: Key | some r : Responsible {
		Ongoing[r]
		r.node = n
		r.key in k
	}}
}

// Visualize Members
fun Visual_Member: Node{
	{(Member & Ongoing).node}
}



/*
 * Sigs:
 * - Value
 * - Node (Key)
 * - Key
*/

sig Key {}

abstract sig Value {}
lone sig Bottom extends Value {}

sig WriteableValue extends Value {}


sig Node extends Key {}

sig Member extends Interval{
	node : one Node
}

sig Responsible extends Interval{
	node : one Node,
	key : set Key,
}{
	some key
}



/* Functional Operations */
abstract sig FunctionalOperation extends Interval {
	node : one Node,
	replier : one Node,
	key : one Key,
} {
	not Singleton[this]
}

sig Store extends FunctionalOperation {
	value: one WriteableValue,
}

sig Lookup extends FunctionalOperation {
	value: one Value,
}

sig FindNode extends FunctionalOperation {
	responsible: one Node,
}


/* Membership Actions*/
abstract sig MembershipOperation extends Interval {
	node: one Node
}


sig Join, Leave extends MembershipOperation{}

sig Fail extends MembershipOperation{}

/* Only Fails are singletons */
fact {
	all op : Join + Leave | not Singleton[op]
	all f : Fail | Singleton[f]
}

/* Regimens and States*/
sig IdealState, ReadOnlyRegimen, StableRegimen extends Interval{}

// Regimens intervals complement the operations
fact {
	Complement[Store, ReadOnlyRegimen]
	Complement[MembershipOperation, StableRegimen]
}

// States and regimens do not overlap
fact {
	all disj id1, id2 : IdealState {
		Before[id1, id2] or After[id1, id2]
	}
	all disj sb1, sb2 : StableRegimen {
		Before[sb1, sb2] or After[sb1, sb2] 
	}
	all disj ro1, ro2 : ReadOnlyRegimen {
		Before[ro1, ro2] or After[ro1, ro2] 
	}
}


// Membership rules
fact {

	// Membership intervals do not overlap
	all disj m1, m2 : Member {
		m1.node = m2.node implies
			Before[m1, m2] or After[m1, m2]
	}

	// Memberships are terminated by failing or leaving
	all departure : Leave + Fail {
		Finite[departure] implies
			one member : Member {
				member.node = departure.node
				(Finishes[departure, member] or Equal[departure, member])
			}
	}
	all member : Member {
		Finite[member] implies
			one departure : Leave + Fail {
				member.node = departure.node
				(Finishes[departure, member] or Equal[departure, member])
			}
	}


	// Nodes become members after joining
	all join : Join {
		Finite[join] iff (one member : Member {
			member.node = join.node
			Meets[join, member]
		})
	}
	all member : Member {
		not Initial[member] implies some join : Join {
			member.node = join.node
			Meets[join, member]
		}
	}
}

/* Check Membership Operations correctly trigger member intervals */
/*
check LeaveEndsMember{
	always all l : Leave {
		Ending[l] implies after( no m : Member{Ongoing[m] and m.node = l.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 FunctionalOperation,
	0 Store, 0 Lookup, 0 Fail expect 0

check FailEndsMember{
	always all f : Fail{
		Ending[f] implies after( no m : Member{Ongoing[m] and m.node = f.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 FunctionalOperation,
	0 Store, 0 Lookup expect 0

check JoinStartsMember{
	always all j : Join{
		Ending[j] implies after( some m : Member{Ongoing[m] and m.node = j.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 FunctionalOperation,
	0 Store, 0 Lookup expect 0
*/

// Axiomatization of action preconditions not covered by event library.
fact {
	// Nodes cannot repeat ongoing operations
	all disj op1, op2 : Store{
		{
			op1.node = op2.node
			op1.key = op2.key
			op1.value = op2.value
		}
		implies
		Precedes[op1, op2] or Precedes[op2, op1]
	}
	all disj op1, op2 : Lookup{
		{
			op1.node = op2.node
			op1.key = op2.key
		}
		implies
		Precedes[op1, op2] or Precedes[op2, op1]
	}
	all disj op1, op2 : FindNode{
		{
			op1.node = op2.node
			op1.key = op2.key
		}
		implies
		Precedes[op1, op2] or Precedes[op2, op1]
	}

	all disj op1, op2 : Join{
		op1.node = op2.node
		Before[op1, op2] or After[op1, op2]
	}

	all disj op1, op2 : Leave{
		op1.node = op2.node
		Before[op1, op2] or After[op1, op2]
	}


	all disj f1, f2 : Fail{
		f1.node = f2.node
		Before[f1, f2] or After[f1, f2] 
	}

	// Nodes must be members to:
	// - initiate funcional operations
    // - fail
    // - leave

	all op : FunctionalOperation | some member : Member {
		op.node = member.node
		Requires[op, member]
	}

	all fail : Fail | some member : Member {
		member.node = fail.node 
		Finishes[fail, member]
	}
	
	all leave : Leave | some member : Member {
		leave.node = member.node
		Requires[leave, member]
	}

	// Nodes must not be members to join the network
	all join : Join | no member : Member {
		member.node = join.node
		--Intersects[join, member]
		Requires[join, member]
	}
	
}

/*
 * Functional Properties of DHT Axiomatization
 */
pred Axioms{
	// Value Properties
	LookupConsistency
	ValueConsistency
	ValueFreshness
//	WeakValueFreshness (implied by ValueFreshness)
	
	// Key Properties
	KeyConsistency
	FindNodeLookupConsistency 
	ResponsibilityExpiration
	ResponsibilityTransfer 

	// Structural Properties
	Reachability
	MembershipGuarantee 
	TerminationCompleteness
}

/*
 * Value Properties
 */


/* P1 Lookup Consistency
 * If a lookup reads a key-value pair, 
 * then it was previously written by a store operation. 
 */
pred LookupConsistency {
	all lookup : Lookup {
		(lookup.value != Bottom && Finite[lookup]) implies 
			some store : Store {
				store.key = lookup.key
				store.value = lookup.value

				not Precedes[lookup, store]
			}
	}
}

pred LookupConsistencyPrecondition {
	some lookup : Lookup | lookup.value != Bottom && Finite[lookup]
}

/* P2 Value Consistency
 * In an Ideal state during a ReadOnly regimen, all lookup
 * operations for a given key return the same value.
 */
pred ValueConsistency {
	all disj lookup1, lookup2 : Lookup, 
		readOnly : ReadOnlyRegimen, ideal : IdealState {
		{
			lookup1.key = lookup2.key
			Finite[lookup1]
			Finite[lookup2]
			In[lookup1, readOnly] or Equal[lookup1, readOnly]
			In[lookup2, readOnly] or Equal[lookup2, readOnly]
			In[lookup1, ideal] or Equal[lookup1, ideal]
			In[lookup2, ideal] or Equal[lookup2, ideal]
		}
		implies lookup1.value = lookup2.value 
	}
}

pred ValueConsistencyPrecondition {
	some disj lookup1, lookup2 : Lookup, 
		readOnly : ReadOnlyRegimen, ideal : IdealState {
			lookup1.key = lookup2.key
			Finite[lookup1]
			Finite[lookup2]
			In[lookup1, readOnly] or Equal[lookup1, readOnly]
			In[lookup2, readOnly] or Equal[lookup2, readOnly]
			In[lookup1, ideal] or Equal[lookup1, ideal]
			In[lookup2, ideal] or Equal[lookup2, ideal]
		}
}

/* P3 Value Freshness
 * In an Ideal state all lookup operations for a key return the
 * value written by the write operation that most recently terminated, or one of
 * its concurrent write operations, or an ongoing write operation.
 */
pred ValueFreshness {
	all lookup: Lookup {
		{ 
			lookup.value != Bottom
			some ideal : IdealState {
				Finite[lookup]
				In[lookup, ideal] or Equal[lookup, ideal]
			}
		}
		implies some store : Store {
			lookup.value = store.value
			lookup.key = store.key

			// Concurrent
			Intersects[store, lookup]

			or
			
			(Precedes[store, lookup] and
			all store2 : Store - store {
				(store2.key = store.key and
				Precedes[store2, lookup])
				implies
					not Precedes[store, store2]
			})
		}
	}

}

pred ValueFreshnessPrecondition {
	some lookup: Lookup, ideal : IdealState {
		lookup.value != Bottom
		Finite[lookup]
		In[lookup, ideal] or Equal[lookup, ideal]
	}
}

/* P3 Weak Value Freshness
 * In an Ideal state and during a ReadOnly regimen, 
 * all lookup operations for a given key return the value written by the write
 * operation that most recently started or one of its concurrent write operations
 */
pred WeakValueFreshness {
	all lookup: Lookup {
		{
			lookup.value != Bottom
			some ideal : IdealState, readOnly : ReadOnlyRegimen {
				Finite[lookup]
				In[lookup, ideal] or Equal[lookup, ideal]
				In[lookup, readOnly] or Equal[lookup, readOnly]
			}
		}
		implies some store : Store { 
			lookup.value = store.value 
			lookup.key = store.key 
			Precedes[store, lookup]

			all store2 : Store - store {
				(store2.key = store.key and
				Precedes[store2, lookup])
				implies
					not Precedes[store, store2]
			}
		}
	}
}

pred WeakValueFreshnessPrecondition {
	some lookup: Lookup, ideal : IdealState, readOnly : ReadOnlyRegimen {
		lookup.value != Bottom
		Finite[lookup]
		In[lookup, ideal] or Equal[lookup, ideal]
		In[lookup, readOnly] or Equal[lookup, readOnly]
	}
}

/*
 * Key Properties
 */


/* P4 Key Consistency
 * In an Ideal state and Stable regimen, all members agree
 * about which member is responsible for a key.
 */
pred KeyConsistency {
	all ideal : IdealState, stable : StableRegimen, disj find1, find2 : FindNode {
		{
			find1.key = find2.key
			Finite[find1]
			Finite[find2]
			In[find1, ideal] or Equal[find1, ideal]
			In[find2, ideal] or Equal[find2, ideal]
			In[find1, stable] or Equal[find1, stable]
			In[find2, stable] or Equal[find2, stable]
		}
		implies find1.responsible = find2.responsible
	}
}

pred KeyConsistencyPrecondition{
	some ideal : IdealState, stable : StableRegimen, disj find1, find2 : FindNode {
		find1.key = find2.key
		Finite[find1]
		Finite[find2]
		In[find1, ideal] or Equal[find1, ideal]
		In[find2, ideal] or Equal[find2, ideal]
		In[find1, stable] or Equal[find1, stable]
		In[find2, stable] or Equal[find2, stable]
	}
}


/* P5 FindNode Lookup Consistency
 * If the lookup of key k returns a value stored by node n,
 * then n must have been responsible for key k in at least one instant.
 * 
 * If the findnode of key k returns a node n,
 * then n must have been responsible for key k in at least one instant.
 */
pred FindNodeLookupConsistency {
	all find: FindNode {
		Finite[find] implies some r : Responsible {
			r.node = find.responsible
			find.key in r.key
			Intersects[r, find] or Precedes[r, find]
		}
	}
	all look: Lookup{
		Finite[look] implies some r : Responsible {
			r.node = look.replier
			look.key in r.key
			Intersects[r, look] or Precedes[r, look]
		}
	}
}

pred FindNodeLookupConsistencyPrecondition {
	some op: FindNode + Lookup | Finite[op]
}


/* P6 Responsibility Expiration
 * When a node fails and does not rejoin,
 * it eventually stops being responsible for any key
 */
pred ResponsibilityExpiration {
	all fail : Fail {
		(no join : Join {
			join.node = fail.node	
			Precedes[fail, join]
		})
		
		implies no r : Responsible {
			fail.node = r.node
			not Finite[r]
		}
	}
}

pred ResponsibilityExpirationPrecondition {
	some fail : Fail | no join : Join {
			join.node = fail.node	
			Precedes[fail, join]
	}
}


/* P7 Responsibility Transfer
 * When a node leaves the network
 * it immediately ceases to be responsible for any key
 */

pred ResponsibilityTransferV2{
	all leave: Leave, n : Leave.node, find : FindNode {
		(
		find.responsible = n and
		Precedes[leave, find]
		)
		implies
		(
		some join : Join {
			join.node = n
			Precedes[find, join]
		})
	}
}

pred ResponsibilityTransferV3{
	all leave: Leave, n : Leave.node, find : FindNode {
		(
		find.responsible = n and
		Precedes[leave, find]
		)
		implies
		(
		some join : Join {
			join.node = n
			Precedes[join, find]
			Precedes[leave, join]
		})
	}
}

pred ResponsibilityTransfer{
	all leave: Leave, n : Leave.node {
		(no join : Join {
			Precedes[leave, join]
			join.node = leave.node // Was missing
		})
		implies no find: FindNode {
			find.responsible = n

			Precedes[leave, find]
		}
	}
}

/*pred ResponsibilityTransfer{
	all leave: Leave, n : Leave.node {
		no find: FindNode, join : Join {
			find.responsible = n
			join.node = n

			Precedes[leave, find]
			Precedes[find, join]

		}
	}
}*/



pred ResponsibilityTransferPrecondition{
	some leave: Leave, n : Leave.node, find : FindNode {
		find.responsible = n
		Precedes[leave, find]
	}
}


pred ResponsibilityTransferV2Precondition{
	ResponsibilityTransferPrecondition
}

pred ResponsibilityTransferV3Precondition{
	ResponsibilityTransferPrecondition
}


/*
 * Structure Properties
 */

/* P8 Membership Guarantee
 * FindNode operations must return a node that was a
 * member at one instant during the execution of the operation
 * The replier of an operation must have been a member
 * at one instant during the execution of the operation
 */
pred MembershipGuarantee {
	all find: FindNode {
		Finite[find] implies
			some member : Member {
				member.node = find.responsible
	
				(Intersects[find, member] or
					Precedes[member, find])
			}
	}
	all op: FunctionalOperation {
		Finite[op] implies
			some member : Member {
				member.node = op.replier
				(Intersects[op, member] or
					Precedes[member, op])
			}
	}
	--MembershipGuarantee_Responsible
	--MembershipGuarantee_Replier
}
/*
check MemberCheck{
 (MembershipGuarantee_Responsible and MembershipGuarantee_Replier) implies MembershipGuarantee
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0 
*/
/*pred MembershipGuarantee_FindNode {
	all find: FindNode {
		Finite[find] implies
			some m : Member {
				m.node = find.responsible
				Intersects[m, find]
			}
	}
}*/

pred MembershipGuarantee_Responsible {
	all find: FindNode {
		Finite[find] implies{
			(some member : Member {
				member.node = find.responsible
				Initial[member]
				no exit : Leave + Fail {
					exit.node = find.responsible
					Precedes[exit, find]
				}
			})
			or
			(some j : Join {
				(Precedes[j, find] or
				Intersects[find, j]
				)
				j.node = find.responsible
				no exit : Leave + Fail {
					exit.node = find.responsible
					Precedes[j, exit]
					Precedes[exit, find]

					/* Responsible node exiting the network simultaneously with
						the start of the FindNode operation is allowed
						to prevent it: */
					/*Starts[exit, find]
					Starts[find, exit]*/
					
				}
			})
		}
	}
}

pred MembershipGuarantee_ResponsiblePrecondition {
	some find: FindNode | Finite[find]
}

/*
pred MembershipGuarantee_Replier {
	all op: FunctionalOperation {
		Finite[op] implies
			some m : Member {
				m.node = op.replier
				Intersects[m, op]
			}
	}
}*/

pred MembershipGuarantee_Replier {
	all op: FunctionalOperation {
		Finite[op] implies {
			(some member : Member {
				member.node = op.replier
				Initial[member]
				no exit : Leave + Fail {
					exit.node = op.replier
					Precedes[exit, op]
				}
			})
			or
			(some j : Join {
				(Precedes[j, op] or
				Intersects[op, j]
				)
				j.node = op.replier
				no exit : Leave + Fail {
					exit.node =op.replier
					Precedes[j, exit]
					Precedes[exit, op]

					/* Responsible node exiting the network simultaneously with
						the start of the FindNode operation is allowed
						to prevent it: */
					/*Starts[exit, find]
					Starts[find, exit]*/
					
				}
			})
		}
	}
}

pred MembershipGuarantee_ReplierPrecondition {
	some op: FunctionalOperation | Finite[op]
}

/* P9 Reachability
 * If a node n is a member during an Ideal state,
 * then all findNode operations of the key that has 
 * the same value of the identifier of n must return n.
 */
pred Reachability {
	all findNode: FindNode, n : Node & findNode.key {
		{
			Finite[findNode]
			some ideal : IdealState, member : Member {
				member.node = n
				In[member, ideal] or Equal[member, ideal]
				In[findNode, ideal] or Equal[findNode, ideal]
				-- In[findNode, member] or Equal[findNode, member]
			}
		}
		implies findNode.responsible = n
	}
}

pred ReachabilityPrecondition {
	some findNode: FindNode, n : Node & findNode.key, ideal : IdealState, member : Member {
		Finite[findNode]
		member.node = n
		In[member, ideal] or Equal[member, ideal]
		In[findNode, ideal] or Equal[findNode, ideal]
	}
}


/* P10 Termination Completeness
 * During an infinite Stable regimen
 * all operations that start in this regimen will terminate
 */
pred TerminationCompleteness {
	all op: FunctionalOperation, stable : StableRegimen {
		not Finite[stable] and In[op, stable]
		implies Finite[op]
	}
}

pred TerminationCompletenessPrecondition {
	some op: FunctionalOperation, stable : StableRegimen {
		not Finite[stable] and In[op, stable]
	}
}

/* 
 * Runs
 */
/*
run Empty {} for 2  but 0 Key, 0 Value
run Member {
	Axioms
	some Member
} for 4 but 5 Interval

run Store {
	Axioms
	some st : Store | Finite[st]
} for 8 but 1 FunctionalOperation, 5 Interval

run Lookup{
	Axioms
	some l : Lookup | Finite[l]
} for 8 but 2 FunctionalOperation

run LookupWriteable{
	Axioms
	some l : Lookup { Finite[l]
		l.value in WriteableValue
	}
} for 8 but 2 FunctionalOperation

run Lookup_Bottom{
	Axioms
	some l : Lookup { Finite[l]
		l.value = Bottom
	}
} for 8 but 2 FunctionalOperation

run FindNode{
	Axioms
	some find : FindNode| Finite[find]
} for 8 but 1 FunctionalOperation

run Fail{
	Axioms
	some f : Fail | Finite[f]
} for 6

run Join{
	Axioms
	some j : Join | Finite[j]
} for 6 but 4 Interval

run Leave{
	Axioms
	some l : Leave{
		Finite[l]
		no m : Member | Equal[m, l]
	}
} for 6

run Ideal {
	Axioms
	some IdealState
} for 4

run Stable {
	Axioms
	some StableRegimen
} for 6

run ReadOnly {
	Axioms
	some ReadOnlyRegimen
} for 6


/*
 * Valid Scenarios 
 */


run S1_AllNodesParticipate{
	Axioms
	MembershipOperation.node + FunctionalOperation.node = Node
	#Node > 2
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S2_AllNodesParticipateFinite{
	Axioms
	MembershipOperation.node + FunctionalOperation.node = Node
	all op : FunctionalOperation + MembershipOperation{
		Finite[op]
	}
	#Node > 2
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1



run S3_AllNodesParticipateOrFail{
	Axioms
	(FunctionalOperation.node + Fail.node) = Node
	some Fail
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S4_ConcurrentLookup{
	Axioms
	some disj look1, look2 : Lookup {
		Intersects[look1, look2]
		Finite[look1]
		Finite[look2]
		look1.key = look2.key
		look1.value != look2.value
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S5_AllOperations{
	Axioms
	some Lookup
	some Store
	some FindNode
	some Join
	some Leave
	some Fail
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S6_AllFunctionalOperationsTerminate{
	Axioms
	some Lookup
	some Store
	some FindNode
	all i : FunctionalOperation | Finite[i]
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S7_ConcurrentLookupStore {
	Axioms
	some lookup : Lookup, store : Store {
		Finite[lookup]
		Finite[store]
		Intersects[lookup, store]
		lookup.value = store.value
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S8_FindNode_After_Leave {
	Axioms
	some leave: Leave, find: FindNode {
		leave.node = find.responsible
		Finite[find]

		(Precedes[leave,find] or
		Overlap[leave, find] or 
		During[leave, find] or
		Starts[leave, find]
		)

		no join : Join {
			join.node = leave.node
		}
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S9_FindNode_After_Fail{
	Axioms
	some fail: Fail, find: FindNode {
		fail.node = find.responsible
		Finite[find]
		Precedes[fail,find] or During[fail, find] or Starts[fail, find]
		no join : Join {
			join.node = fail.node
		}
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


run S10_Find_Node_of_Departed_Node {
	Axioms
	some leave: Leave, find: FindNode {
		leave.node = find.key
		Finite[find]
		Precedes[leave,find]
		no join : Join {
			join.node = leave.node
		}
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


/* 
 * Derived Assertions
 */

assert A1_No_Member_Operations {
	(Axioms and some FunctionalOperation) implies some Member
}


assert A2_Lookup_Stale_Value{
	(Axioms and
	one ideal : IdealState {
		all operation : FunctionalOperation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies
	no store1, store2 : Store, lookup : Lookup{
		store1.key = store2.key
		store1.value != store2.value
		Precedes[store1, store2]
		
		no store3 : Store - store1 { 
			store3.key = store1.key 
			store3.value = store1.value 
		}
		Precedes[store2, lookup]
		lookup.key = store1.key
		lookup.value = store1.value
		Finite[lookup]
	}
}


assert A3_ValueFreshness_Implies_WeakValueFreshness{
	ValueFreshness implies WeakValueFreshness
}

assert A4_ValueFreshness_Implies_LookupConsistency{
	(ValueFreshness and one ideal : IdealState {
		all operation : FunctionalOperation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies LookupConsistency
}
 
check A1_No_Member_Operations for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0


check A2_Lookup_Stale_Value for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0


check A3_ValueFreshness_Implies_WeakValueFreshness for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0


check A4_ValueFreshness_Implies_LookupConsistency for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0

/*
check A1_No_Member_Operations for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 0

check A2_Lookup_Stale_Value for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 0

check A3_ValueFreshness_Implies_WeakValueFreshness for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 0

check A4_ValueFreshness_Implies_LookupConsistency for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 0

check A1_No_Member_Operations for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0


check A2_Lookup_Stale_Value for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0


check A3_ValueFreshness_Implies_WeakValueFreshness for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0


check A4_ValueFreshness_Implies_LookupConsistency for 
	10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0
*/
