open ATL

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
	 ATL/C_Ongoing - Member - Responsible
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
	all op : Join + Leave /* + Operatoin */ | not Singleton[op]
	all f : Fail | Singleton[f]
}

/* Regimens and States*/
sig IdealState, ReadOnlyRegimen, StableRegimen extends Interval{}

fact {

	--	Complement[Store, ReadOnlyRegimen]
	always {
		(no store : Store | Ongoing[store]) iff
			(some readOnly : ReadOnlyRegimen | Ongoing[readOnly])
	}

	always {
		(no op : Fail + Join + Leave | Ongoing[op]) iff
			(some stable : StableRegimen | Ongoing[stable])
	}


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
	all member : Member {
		Finite[member] iff 
		(
			(one fail : Fail {
				fail.node = member.node
				Finishes[fail, member]
			})
			or
			(one leave : Leave{
				leave.node = member.node
				Finishes[leave, member] or Equal[leave, member]
				
			})
		)
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
fact Axioms{
	KeyConsistency
	LookupConsistency
	ValueConsistency

	ValueFreshness
//	WeakValueFreshness

	Reachability
	MembershipGuarantee 
	ReplyMembershipGuarantee
	
	FindNodeLookupConsistency 

	ResponsabilityTransfer 
//	ResponsabilityExpiration

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
 */
pred MembershipGuarantee {
	all find: FindNode, n : FindNode.responsible {
		Finite[find] implies
			some m : Member {
				m.node = n
				Intersects[m, find]
			}
	}
}


/*
 * P* The replier of an operation must have been a member
 * at one instant during the execution of the operation
 */
pred ReplyMembershipGuarantee {
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
			r.key in find.key
			Intersects[r, find]
		}
	}
	all look: Lookup{
		Finite[look] implies some r : Responsible {
			r.node = look.replier
			r.key in look.key
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
		
		implies all r : Responsible {
			r.node = fail.node
			Finite[r]
		}
	}
}


/* P9 Responsability Transfer
 * When a node leaves the network
 * it immediately ceases to be responsible for any key
 */
pred ResponsabilityTransfer{
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

run Member {
	some Member
} for 4 but 5 Interval

run Store {
	some st : Store | Finite[st]
} for 8 but 1 Operation, 5 Interval

run Lookup{
	some l : Lookup | Finite[l]
} for 8 but 2 Operation

run FindNode{
	some find : FindNode| Finite[find]
} for 8 but 1 Operation

run Fail{
	some f : Fail | Finite[f]
} for 4

run Join{
	some j : Join | Finite[j]
} for 6 but 4 Interval

run Leave{
	some l : Leave{
		Finite[l]
		no m : Member | Equal[m, l]
	}
} for 6

run Ideal {
	some IdealState
} for 4

run Stable {
	some StableRegimen
} for 6

run ReadOnly {
	some ReadOnlyRegimen
} for 6


run ConcurrentLookup {
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
} for 18 Boundary, 
		exactly 2 Lookup, exactly 2 Store,
		0 Fail, 0 MembershipOperation, 0 FindNode,
		exactly 4 Key, exactly 2 Value, exactly 3 Node, exactly 3 Member,
		exactly 1 IdealState, exactly 1 StableRegimen,
		1 ReadOnlyRegimen,
		11 Interval, 0 Proposition
 

/* Axiom tests */
// P1 Key Consistency
run Key_Consistency{
	some disj f1, f2 : FindNode, ideal : IdealState{
		In[f1, ideal]
		In[f2, ideal]
		Finite[f1]
		Finite[f2]
		f1.key = f2.key
	}
} for 8 but 2 FindNode, 1 IdealState

check Key_Consistency{ 
	no disj f1, f2 : FindNode, ideal : IdealState {
		Finite[f1]
		Finite[f2]
		
		In[f1, ideal] or Equal[f1, ideal]
		In[f2, ideal] or Equal[f2, ideal]
		
		f1.key = f2.key
		f1.responsible != f2.responsible
	}
} for 8 but 2 Node, 3 Key, 2 FindNode, 1 IdealState

// P2 Lookup Consistency
check LookupConsistency {
	(some lookup : Lookup | Finite[lookup])
	implies
		some Store
} for 8 but 6 Interval, 12 Boundary

// P3 Value Consistency
run Value_Consistency{
	some disj lookup1, lookup2 : Lookup, readOnly : ReadOnlyRegimen {
		lookup1.key = lookup2.key
		In[lookup1, readOnly] or Equal[lookup1, readOnly]
		In[lookup2, readOnly] or Equal[lookup2, readOnly]
		Finite[lookup1]
		Finite[lookup2]
	}
} for 8 but 1 Key, 2 Value, 3 Operation, exactly 2 Lookup, exactly 1 ReadOnlyRegimen

// P4 Value Freshness
run Value_Freshness{
	some look : Lookup, ideal : IdealState | In[look, ideal]
} for 8 but 3 Operation, exactly 2 Store, exactly 1 Lookup

run Weak_Value_Freshness{
	WeakValueFreshnessCondition
	some Lookup
	 
} for 8 but 3 Operation, exactly 2 Store, exactly 1 Lookup

// Comment LookupConsistency for check
check ValueFreshness_Implies_LookupConsistency{
	(Initial[IdealState] and not Finite[IdealState]
	and ValueFreshness) implies LookupConsistency
} for 8 but 1 Key, 2 Value, 1 Node, 1 Lookup, 0 FindNode,
			exactly 1 IdealState, 0 MembershipOperation

// Comment LookupConsistency for WeakValueFreshness for check
check ValueFreshness_Implies_WeakValueFreshness{
	ValueFreshness implies WeakValueFreshness
} for 8 but 2 Key, 2 Value, 1 Node, 1 Lookup, 0 FindNode,
		0 MembershipOperation

// P5 Reachability
run Reachability{
	some findNode : FindNode, ideal : IdealState, member : Member{
		Finite[findNode]
		findNode.key in Node

		In[findNode, ideal] or Equal[findNode, ideal]
		member.node = findNode.key

		In[ideal, member] or Equal[ideal, member]
	}
} for 8 but 1 Operation, 2 Key, 2 Node, 
		exactly 1 FindNode, exactly 1 IdealState, 0 MembershipOperation 

check Reachability{
	all findNode : FindNode, ideal : IdealState {
		{
		findNode.key in Node
		In[findNode, ideal] or Equal[findNode, ideal]
		findNode.responsible != findNode.key
		}
		implies 
			not Finite[findNode] or 
			no member : Member {
				member.node = findNode.key
				In[ideal, member] or Equal[member, ideal]
			}
	}
} for 8 but 1 Operation, 2 Key, 2 Node , exactly 1 FindNode, exactly 1 IdealState

// P6 Membership Guarantee

// The responsible node obtained in a findNode operation
// was never a member only if the find node operation does not terminate
check Membership_Guarantee{
	all find : FindNode, member : Member{
		{
			member.node = find.responsible

			//not Occurs[member, find]
			Before[member, find] or Meets[member, find]
			or Before[find, member] or Meets[find, member]
		}
		implies not Finite[find]
	}
} for 4




// P10 Termination Completeness
run TerminationCompleteness {
	some op: Operation, stable : StableRegimen {
		not Finite[stable] and In[op, stable]
	}
} for 6

check TerminationCompleteness {
	all op: Operation, stable : StableRegimen {
		(not Finite[op] and In[op, stable]) implies
			Finite[stable]
	}
 
} for 6 but 1 Key, 1 Value
