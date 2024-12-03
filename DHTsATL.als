open ATL

/*open util/ordering[Lookup] as lo
open util/ordering[Store] as so
open util/ordering[Value] as vo
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
 *  - Reply Membership Guarantee
 *  - FindNode Lookup Consistency
 *  - Responsibility Expiration
 *  - Responsibility Transfer
 *  - Termination Completeness
*/

/*
 * Sigs:
 * - Node
 * - Key
 * - Value
*/

sig Key, Value {}

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
abstract sig Operation extends Interval {
	node : one Node,
	replier : one Node,
	key : one Key,
} {
	not Singleton[this]
}

sig Store extends Operation {
	value: one Value,
}

sig Lookup extends Operation {
	value: one Value,
}

sig FindNode extends Operation {
	responsible: one Node,
}


/* Membership Actions*/
abstract sig MembershipOperation extends Interval {
	node: one Node
}


sig Join, Leave extends MembershipOperation{}

sig Fail extends MembershipOperation{}


fact {
	all op : Join + Leave | not Singleton[op]
	all f : Fail | Singleton[f]
}

/* Regimens and States*/
sig IdealState, ReadOnlyRegimen, StableRegimen extends Interval{}

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
/*	all member : Member {
		Finite[member] iff 
		(
			(one fail : Fail {
				Finite[fail]
				fail.node = member.node
				Finishes[fail, member] or Equal[fail, member]
			})
			or
			(one leave : Leave{
				Finite[departure]
				leave.node = member.node
				Finishes[leave, member] or Equal[leave, member]
			})
		)
	}*/

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

/* Check Membership Operations trigger member intervals */
/*
check LeaveEndsMember{
	always all l : Leave {
		Ending[l] implies after( no m : Member{Ongoing[m] and m.node = l.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 Operation,
	0 Store, 0 Lookup, 0 Fail

check FailEndsMember{
	always all f : Fail{
		Ending[f] implies after( no m : Member{Ongoing[m] and m.node = f.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 Operation,
	0 Store, 0 Lookup

check JoinStartsMember{
	always all j : Join{
		Ending[j] implies after( some m : Member{Ongoing[m] and m.node = j.node})
	}
} for 10 but exactly 1 Node, 1 Key,
	10 Interval, 15 Boundary, 0 Operation,
	0 Store, 0 Lookup
*/

// Axiomatization of action preconditions 
// not covered by event library.
fact {
	// Nodes can't repeat operations while ongoing
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

	all op : Operation | some member : Member {
		op.node = member.node
		Initiates[member, op]
	}

	all fail : Fail | some member : Member {
		member.node = fail.node 
		Finishes[fail, member]
	}
	
	all leave : Leave | some member : Member {
		leave.node = member.node
		Initiates[member, leave]
	}

	// Nodes must not be members to join the network
	all join : Join | no member : Member {
		member.node = join.node
		Initiates[member, join]
	}
	
}


/*
 * Axioms
 */
pred Axioms{
	KeyConsistency
	LookupConsistency
	ValueConsistency

	ValueFreshness
//	WeakValueFreshness

	Reachability
	MembershipGuarantee 
		
	FindNodeLookupConsistency 

	ResponsibilityTransfer 
	ResponsibilityExpiration

	TerminationCompleteness
}


/* P1 Key Consistency
 * In an Ideal state and Stable regimen, all members agree
 * about which member is responsible for a key.
 */
pred KeyConsistency {
	all ideal : IdealState, find1, find2 : FindNode {
		{
			find1.key = find2.key
			Finite[find1]
			Finite[find2]
			In[find1, ideal] or Equal[find1, ideal]
			In[find2, ideal] or Equal[find2, ideal]
		}
		implies find1.responsible = find2.responsible
	}
}

/* P2 Lookup Consistency
 * If a lookup reads a key-value pair, 
 * then it was previously written by a store operation. 
 */
pred LookupConsistency {
	all lookup : Lookup {
		Finite[lookup] implies 
			some store : Store {
				store.key = lookup.key
				store.value = lookup.value

				not Precedes[lookup, store]
			}
	}
}

/* P3 Value Consistency
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


/* P4 Value Freshness
 * In an Ideal state all lookup operations for a key return the
 * value written by the write operation that most recently terminated, or one of
 * its concurrent write operations, or an ongoing write operation.
 */
pred ValueFreshness {
	all lookup: Lookup {
		{ 
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

/* P4 Weak Value Freshness
 * In an Ideal state and during a ReadOnly regimen, 
 * all lookup operations for a given key return the value written by the write
 * operation that most recently started or one of its concurrent write operations
 */
pred WeakValueFreshness {
	all lookup: Lookup {
		{
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

pred WeakValueFreshnessCondition {
	all lookup: Lookup | some ideal : IdealState, readOnly : ReadOnlyRegimen {
			Finite[lookup]
			In[lookup, ideal] or Equal[lookup, ideal]
			In[lookup, readOnly] or Equal[lookup, readOnly]
	}
}

/* P5 Reachability
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
				In[ideal, member] or Equal[ideal, member]
				In[findNode, ideal] or Equal[findNode, ideal]
			}
		}
		implies findNode.responsible = n
	}
}

/* P6 Membership Guarantee
 * FindNode operations must return a node that was a
 * member at one instant during the execution of the operation
 * The replier of an operation must have been a member
 * at one instant during the execution of the operation
 */
pred MembershipGuarantee {
	all find: FindNode, n : FindNode.responsible {
		Finite[find] implies
			some m : Member {
				m.node = n
				Intersects[m, find]
			}
	}

	all op: Operation {
		Finite[op] implies
			some m : Member {
				m.node = op.replier
				Intersects[m, op]
			}
	}
}


/* P7 FindNode Lookup Consistency
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
			Intersects[r, find]
		}
	}
	all look: Lookup{
		Finite[look] implies some r : Responsible {
			r.node = look.replier
			look.key in r.key
			Intersects[r, look]
		}
	}
}

/* P8 Responsibility Expiration
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


/* P9 Responsibility Transfer
 * When a node leaves the network
 * it immediately ceases to be responsible for any key
 */
pred ResponsibilityTransfer{
	all leave: Leave, n : Leave.node {
		(no join : Join {
			Precedes[leave, join]
		})
		implies no find: FindNode {
			find.responsible = n

			Precedes[leave, find]
		}
	}
}

/* P10 Termination Completeness
 * During an infinite Stable regimen
 * all operations that start in this regimen will terminate
 */
pred TerminationCompleteness {
	all op: Operation, stable : StableRegimen {
		not Finite[stable] and In[op, stable]
		implies Finite[op]
	}
}

/* 
 * Runs
 */
/*
run Member {
	Axioms
	some Member
} for 4 but 5 Interval

run Store {
	Axioms
	some st : Store | Finite[st]
} for 8 but 1 Operation, 5 Interval

run Lookup{
	Axioms
	some l : Lookup | Finite[l]
} for 8 but 2 Operation

run FindNode{
	Axioms
	some find : FindNode| Finite[find]
} for 8 but 1 Operation

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
*/

/* Valid Scenarios */
run AllNodesParticipate{
	Axioms
	MembershipOperation.node + Operation.node = Node
	#Node > 2
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
--} for 8 but exactly 3 Node, 2 Key, 2 Value expect 1

run AllNodesParticipateFinite{
	Axioms
	MembershipOperation.node + Operation.node = Node
	all op : Operation + MembershipOperation{
		Finite[op]
	}
	#Node > 2
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
--} for 8 but exactly 2 Node, 2 Key, 2 Value expect 1


run AllNodesParticipateOrFail{
	Axioms
	(Operation.node + Fail.node) = Node
	some Fail
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
--} for 8 but 3 Node, 2 Key, 2 Value expect 1

run ConcurrentLookup{
	Axioms
	some disj look1, look2 : Lookup {
		Intersects[look1, look2]
		Finite[look1]
		Finite[look2]
		look1.key = look2.key
		look1.value != look2.value
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
/*} for 4 but 18 Boundary, 10 Interval,
		exactly 2 Lookup, exactly 2 Store
		0 Fail, 0 MembershipOperation, 0 FindNode,
		exactly 4 Key, exactly 2 Value, exactly 3 Node, exactly 3 Member,
		exactly 1 IdealState, exactly 1 StableRegimen,
		1 ReadOnlyRegimen,*/


run ConcurrentLookupStable{
	Axioms

	some disj s1, s2: Store{
		not	Initiates[s1, s2]
	}
	
	some l : Lookup {
		Ongoing[l]
	}


	//Visualization order
/*	lo/first.value = vo/first
	so/first.value = vo/first
	Initiates[lo/first, lo/last] or Precedes[lo/first, lo/last]
	Initiates[so/first, so/last] or Precedes[so/first, so/last]*/

	some disj look1, look2 : Lookup {
		Intersects[look1, look2]
		Finite[look1]
		Finite[look2]
		look1.key = look2.key
		look1.key not in Node
		look1.value != look2.value
	}
//} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1


} for 4 but 3 Boundary, 12 Interval,
		exactly 2 Lookup, exactly 2 Store, exactly 3 Node, 5 Key, 2 Value,
		0 Fail, 0 MembershipOperation, exactly 3 Member/*, 0 FindNode,
		exactly 4 Key, exactly 2 Value, exactly 3 Node, exactly 3 Member,
		exactly 1 IdealState, exactly 1 StableRegimen,
		1 ReadOnlyRegimen,P/

run AllOperations{
	Axioms
	some Lookup
	some Store
	some FindNode
	some Join
	some Leave
	some Fail
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
/*} for 3 but 1 Node, 1 Key, 1 Value, exactly 1 Lookup, exactly 1 Store,
		exactly 1 FindNode, exactly 1 Join, exactly 1 Leave, exactly 1 Fail,
		10 Interval, 8 Boundary*/

/*
run AllOperationsTerminate{
	Axioms
	some Lookup
	some Store
	some FindNode
	some Join
	some Leave
	some Fail
	all i : Operation + MembershipOperation | Finite[i]
--} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
} for 11 Interval, 8 Boundary, 5 Key, 1 Value, 0 Proposition expect 1
*/
run AllFunctionalOperationsTerminate{
	Axioms
	some Lookup
	some Store
	some FindNode
	all i : Operation | Finite[i]
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1

run ConcurrentLookupStore {
	Axioms
	some lookup : Lookup, store : Store {
		Finite[lookup]
		Finite[store]
		Intersects[lookup, store]
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
/*
} for 0 but 2 Node, 1 Key, 2 Value, exactly 1 Lookup, exactly 1 Store, 
	6 Interval, 10 Boundary
*/

run FindNode_After_Leave {
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
/*} for 10 but 2 Node, 2 Key, 0 Value, exactly 1 FindNode, 
	exactly 1 MembershipOperation,
	10 Interval, 15 Boundary,
	0 Store, 0 Lookup*/

run FindNode_After_Fail{
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
/*
} for 10 but exactly 2 Node, 2 Key, 0 Value, exactly 1 FindNode, 
	exactly 1 MembershipOperation,
	10 Interval, 15 Boundary,
	0 Store, 0 Lookup
*/
	
run Find_Node_of_Departed_Node {
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
/*} for 10 but exactly 2 Node, 2 Key, 0 Value, exactly 1 FindNode, 
	exactly 1 MembershipOperation,
	10 Interval, 15 Boundary,
	0 Store, 0 Lookup */


run ConcurrentLookup {
	Axioms
	all	m : Member | Initial[m] and not Finite[m]
	Initial[IdealState] and not Finite[IdealState]

	no look : Lookup {
		Initial[look]
	}
	always {
		#(Ongoing & Operation) < 3
	}
	some disj look1, look2 : Lookup {
		
		--Intersects[look1, look2]
		Finite[look1]
		Finite[look2]
		look1.key = look2.key
		look1.key not in Node

		look1.value != look2.value
	}
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1

/*} for 18 Boundary, 
		exactly 2 Lookup, exactly 2 Store,
		0 Fail, 0 MembershipOperation, 0 FindNode,
		exactly 4 Key, exactly 2 Value, exactly 3 Node, exactly 3 Member,
		exactly 1 IdealState, exactly 1 StableRegimen,
		1 ReadOnlyRegimen,
		11 Interval, 0 Proposition*/
 
/* Invalid Scenarios */
run No_Member_Operations {
	Axioms
	some Operation
	no Member
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0

run Lookup_Stale_Value{
	Axioms
	one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	}

	some store1, store2 : Store, lookup : Lookup{
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
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0
 
/* Derived Properties */
check ValueFreshness_Implies_WeakValueFreshness{
	--(Initial[IdealState] and not Finite[IdealState]
	ValueFreshness implies WeakValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0
/*} for 8 but 1 Key, 2 Value, 1 Node, 1 Lookup, 0 FindNode,
			exactly 1 IdealState, 0 MembershipOperation expect 0*/

check ValueFreshness_Implies_LookupConsistency{
	(ValueFreshness and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies LookupConsistency

--(Initial[IdealState] and not Finite[IdealState]
--	ValueFreshness implies LookupConsistency
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 0
/*} for 8 but 1 Key, 2 Value, 1 Node, 1 Lookup, 0 FindNode,
			exactly 1 IdealState, 0 MembershipOperation expect 0*/

/*
check Lookup_Consistency_Does_Not_Imply_ValueFreshness{
	(LookupConsistency and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies ValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition expect 1
*/

/* 15 Steps */

/* Invalid Scenarios */
run No_Member_Operations {
	Axioms
	some Operation
	no Member
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 0

run Lookup_Stale_Value{
	Axioms
	one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	}

	some store1, store2 : Store, lookup : Lookup{
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
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition,  1..15 steps expect 0
 
/* Derived Properties */

check ValueFreshness_Implies_WeakValueFreshness{
	ValueFreshness implies WeakValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition,  1..15 steps expect 0



check ValueFreshness_Implies_LookupConsistency{
	(ValueFreshness and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies LookupConsistency

} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition,  1..15 steps expect 0


/*
check Lookup_Consistency_Does_Not_Imply_ValueFreshness{
	(LookupConsistency and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies ValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..15 steps expect 1
*/


/** 20 Steps **/

/* Invalid Scenarios */
run No_Member_Operations {
	Axioms
	some Operation
	no Member
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0

run Lookup_Stale_Value{
	Axioms
	one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	}

	some store1, store2 : Store, lookup : Lookup{
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
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0
 
/* Derived Properties */

check ValueFreshness_Implies_WeakValueFreshness{
	ValueFreshness implies WeakValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0


check ValueFreshness_Implies_LookupConsistency{
	(ValueFreshness and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies LookupConsistency

} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 0

/*check Lookup_Consistency_Does_Not_Imply_ValueFreshness{
	(LookupConsistency and one ideal : IdealState {
		all operation : Operation + MembershipOperation {
			In[operation, ideal] or Equal[operation, ideal]
		}
	})
	implies ValueFreshness
} for 10 Interval, 15 Boundary, 5 Key, 5 Value, 0 Proposition, 1..20 steps expect 1
*/

