// SPDX-License-Identifier: MIT
// Copyright (C) 2024 Nuno Policarpo

module ATL

/*
 * Alloy Library for Allen Temporal Logic
 *
 * Signatures: 
 *	  - Proposition
 *    - Boundary
 *    - Interval
 *
 *
 * Variable Signatures:
 *     - Happens 
 *     - Ongoing 
 * 
 * Concrete Signatures for testing
 * 		- T : Interval
 * 		- P : Proposition
 */ 


/* 
 * Signatures
 */

abstract sig Proposition {}
var sig Active in Proposition {}

sig Boundary {}

abstract sig Interval {
	start : one Boundary, 
	end : lone Boundary,
}

var lone sig Happens in Boundary {}

var sig Ongoing in Interval {}


sig T extends Interval{}
sig P extends Proposition{}


/* 
 *  Ongoing Functions
 */

fun Starting : Interval{
	start.Happens
}

fun Ending: Interval{
	end.Happens
}

/*
 * Auxiliary Predicates
 */ 

pred Ongoing[ i : Interval ] {
	i in Ongoing
}

pred Starting[ i : Interval ] {
	i in Starting
}

pred Ending[ i : Interval ] {
	i in Ending
}

pred Active[p : Proposition] {
	p in Active
}

pred Happens[b : Boundary] {
	b in Happens
}

pred Finite[i : Interval] {
	eventually Ending[i]
}

pred Singleton[i : Interval] {
	i.start = i.end
}

pred Initial[i : Interval] {
	Starting[i]
}


/*
 * Auxiliary Predicate Encoding	
 */
fact { 

	// Ongoing intervals in the next state are those that start and
	// the non-terminating currently ongoing intervals
	always{
		Ongoing' = Ongoing + Starting' - Ending
		(Starting + Ending) in Ongoing
	}

	// Intervals start only if they were previously not ongoing
	all i : Interval | always (i in Starting' implies i not in Ongoing)

	// Intervals do not repeat
	all i : Interval | always (Ending[i] implies after always not Starting[i])
}



// Scope limiting facts
fact {

	// All boundaries happen
	all b : Boundary | eventually Happens[b]

	// All boundaries belong to an interval
	Boundary in Interval.(start+end)

}



/* 
 * Interval predicates
 */

// EQUAL(i1, i2): Intervals i1 and i2 are ongoing during the same instants.
pred Equal[i1 : Interval, i2 : Interval] {
	always (Ongoing[i1] iff Ongoing[i2])
}


// BEFORE(i1, i2): Interval i1 ends at least 2 instants before i2 starts
let strong_release [p1, p2] = {eventually p1 and p1 releases p2}

pred Before[i1 : Interval, i2 : Interval] {
	strong_release[	Ending[i1] , not Ongoing[i2]]
	not eventually (Ending[i1] and after Starting[i2])
}

// MEETS(i1, i2): Interval i2 starts imediatelly after i1 ends
pred Meets[i1 : Interval, i2 : Interval] {
	eventually (Ending[i1] and after Starting[i2])
}


// OVERLAP(i1, i2): Interval i1 starts before i2, and they overlap
pred Overlap[i1 : Interval, i2 : Interval] {
	Ongoing[i1] releases not Ongoing[i2]
	eventually (Ending[i1] and Ongoing[i2] and not Ending[i2])
}


// DURING(i1, i2): Interval i1 is strictly contained within i2
pred During[i1 : Interval, i2 : Interval] {
	always {
		Ongoing[i1] implies Ongoing[i2]		
		Starting[i1] implies not Starting[i2]
	}

	// Only finite intervals can be contained
	eventually (Ending[i1] and not Ending[i2])
}


// STARTS(i1, i2): Interval i1 starts simultaneously with i2 
// and ends earlier than i2
pred Starts[i1 : Interval, i2 : Interval] {
	eventually (Starting[i1] and Starting[i2])
	eventually (Ongoing[i2] and not Ongoing[i1])
}

// FINISHES(i1, i2): Interval i1 ends simultaneously with i2 
// and starts later than i2
pred Finishes[i1 : Interval, i2 : Interval] {
	eventually (Ongoing[i2] and not Ongoing[i1])
	always (Ending[i1] iff Ending[i2])
}

/*
 *  Inverted Interval Predicates
 */
pred After[i1 : Interval, i2: Interval] { Before[i2, i1] }

pred DuringI[i1 : Interval, i2: Interval] { During[i2, i1] }

pred OverlapI[i1 : Interval, i2: Interval] { Overlap[i2, i1] }

pred MeetsI[i1 : Interval, i2: Interval] { Meets[i2, i1] }

pred StartsI[i1 : Interval, i2: Interval] { Starts[i2, i1] }

pred FinishesI[i1 : Interval, i2: Interval] { Finishes[i2, i1] }

/*
 * Proposition predicates
 */

// HOLDS(p, i): Proposition p holds throughout interval i
pred Holds[p : Proposition, t : Interval]{
	always (Ongoing[t] implies Active[p])
}

// OCCURS(p, i): Proposition p holds at least once during interval i
pred Occurs[p : Proposition, t : Interval] {
	eventually (Ongoing[t] and Active[p])
}


/*
 * Additional predicates
 */

// In(i1, i2): Interval i1 is contained in i2
pred In[i1 : Interval, i2 : Interval] {
	During[i1, i2] or Starts[i1, i2] or Finishes[i1, i2]
}

// Contains(i1, i2): Interval i1 contains i2
pred Contains[i1 : Interval, i2 : Interval] {
	In[i2, i1]
}

// Precedes(i1, i2): Interval i1 ends before i2 starts
pred Precedes[i1 : Interval, i2 : Interval] {
	Before[i1, i2] or Meets[i1, i2]
}

// Intersects(i1, i2): 
//	Intervals i1 and i2 are ongoing during one common instant
pred Intersects[i1 : Interval, i2 : Interval] {
	Equal[i1,i2] or In[i1,i2] or 
	In[i2,i1] or Overlap[i1, i2] or 
	Overlap[i2,i1]
}

// Requires(i1, i2): Interval i1 starts while i2 is ongoing
// 	i.e i1 requires i2 to be ongoing in order to start;
pred Requires[i1 : Interval, i2 : Interval] {
	Equal[i1, i2] or In[i1, i2] or 
	Overlap[i2, i1] or Starts[i2, i1]
}

// Complement(I1, I2):
//	In every instant either a subset of I_1 is ongoing, 
//	or a subset of I_2 is ongoing, but never both. 
pred Complement[I1 : set Interval, I2 : set Interval] {
	always {
		(no i1: I1 | Ongoing[i1]) iff
			(some i2: I2| Ongoing[i2])
	}
}



/*
 * Interval Predicate Visualization Functions 
 * Used to visualize them as relations
 */
private fun d : set Interval->Interval {{t1, t2 : Interval | During[t1, t2]}}
private fun di : set  Interval->Interval {{t1, t2 : Interval | During[t2, t1]}}

private fun s : set  Interval->Interval {{t1, t2 : Interval | Starts[t1, t2]}}
private fun si : set  Interval->Interval {{t1, t2 : Interval | Starts[t2, t1]}}

private fun f : set Interval->Interval {{t1, t2 : Interval | Finishes[t1, t2]}}
private fun fi : set  Interval->Interval {{t1, t2 : Interval | Finishes[t2, t1]}}

private fun o : set  Interval->Interval {{t1, t2 : Interval | Overlap[t1, t2]}}
private fun oi : set  Interval->Interval {{t1, t2 : Interval | Overlap[t2, t1]}}

private fun m : set  Interval->Interval {{t1, t2 : Interval | Meets[t1, t2]}}
private fun mi : set  Interval->Interval {{t1, t2 : Interval | Meets[t2, t1]}}

private fun b : set  Interval->Interval {{t1, t2 : Interval | Before[t1, t2]}}
private fun bi : set  Interval->Interval {{t1, t2 : Interval | Before[t2, t1]}}

private fun e : set  Interval->Interval {{t1, t2 : Interval | Equal[t1, t2]}}


/*
 * Base Property Checks
 */
check Intervals_Dont_Repeat {
	all t : Interval | always {
		Ongoing[t] implies
			always (not Ongoing[t] implies (always not Ongoing[t]))
	}
} for 4 but 1..5 steps expect 0


/* 
 * Derived Property Checks
 */

let Exclusion [a, b] = not (a and b)

// Pairs of intervals have at most one relation
check Exclusivity {
	all i1, i2 : Interval {
		Exclusion[Starts[i1, i2], During[i1, i2]]

		Exclusion[Finishes[i1, i2], During[i1, i2]]
		Exclusion[Finishes[i1, i2], Starts[i1, i2]]

		Exclusion[Before[i1, i2], During[i1, i2]]
		Exclusion[Before[i1, i2], Starts[i1, i2]]
		Exclusion[Before[i1, i2], Finishes[i1, i2]]

		Exclusion[Overlap[i1, i2], During[i1, i2]]
		Exclusion[Overlap[i1, i2], Starts[i1, i2]]
		Exclusion[Overlap[i1, i2], Finishes[i1, i2]]
		Exclusion[Overlap[i1, i2], Before[i1, i2]]

		Exclusion[Meets[i1, i2], During[i1, i2]]
		Exclusion[Meets[i1, i2], Starts[i1, i2]]
		Exclusion[Meets[i1, i2], Finishes[i1, i2]]
		Exclusion[Meets[i1, i2], Before[i1, i2]]
		Exclusion[Meets[i1, i2], Overlap[i1, i2]]


		Exclusion[Equal[i1, i2], During[i1, i2]]
		Exclusion[Equal[i1, i2], Starts[i1, i2]]
		Exclusion[Equal[i1, i2], Finishes[i1, i2]]
		Exclusion[Equal[i1, i2], Before[i1, i2]]
		Exclusion[Equal[i1, i2], Overlap[i1, i2]]
		Exclusion[Equal[i1, i2], Meets[i1, i2]]
	}
} for exactly 2 Interval, 4 Boundary, 0 Proposition expect 0


// Pairs of intervals have at least one relation
check MinimumRelation{
	all i1, i2 : Interval {
		(
		During[i1, i2] or During[i2, i1]
		or
		Starts[i1, i2] or Starts[i2, i1]
		or
		Finishes[i1, i2] or Finishes[i2, i1]
		or
		Before[i1, i2] or Before[i2, i1]
		or
		Overlap[i1, i2] or Overlap[i2, i1]
		or
		Meets[i1, i2] or Meets[i2, i1]
		or
		Equal[i1,i2]
		)
	}
} for exactly 2 Interval, 4 Boundary, 0 Proposition expect 0


/*
 * Interval Predicate Transitivity Properties
 */

// Before
check T_Before {
	all i1, i2, i3 : Interval {
		(Before[i1, i2] and 
			(During[i2, i3] or 
			OverlapI[i2, i2] or 
			MeetsI[i2, i2] or 	
			Finishes[i2, i3]))
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}

		(Before[i1, i2] and 
			(Before[i2, i3] or 
			DuringI[i2, i3] or 
			Overlap[i2, i3] or 	
			Meets[i2, i3] or 
			Starts[i2, i3] or 
			StartsI[i2, i3] or 
			FinishesI[i2, i3]))
		implies {
			Before[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// After
check T_After {
	all i1, i2, i3 : Interval {
		(After[i1, i2] and 
			(During[i2, i3] or 
			Overlap[i2, i3] or 
			Meets[i2, i3] or 	
			Starts[i2, i3] or 	
			Finishes[i2, i3]))
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}

		(After[i1, i2] and 
			(After[i2, i3] or 
			DuringI[i2, i3] or 
			OverlapI[i2, i3] or 	
			MeetsI[i2, i3] or 
			StartsI[i2, i3] or 
			Finishes[i2, i3] or
			FinishesI[i2, i3]))
		implies {
			After[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// During
check T_During {
	all i1, i2, i3 : Interval {
		(During[i1, i2] and 
			(Before[i2, i3] or 
			Meets[i2, i3]))
		implies {
			Before[i1, i3]
		}

		(During[i1, i2] and 
			(After[i2, i3] or 
			MeetsI[i2,i3]))
		implies {
			After[i1, i3]
		}

		(During[i1, i2] and 
			(During[i2, i3] or 
			Starts[i2,i3] or
			Finishes[i2,i3]))
		implies {
			During[i1, i3]
		}

		(During[i1, i2] and 
			(Overlap[i2, i3] or
			FinishesI[i2,i3]))
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}

		(During[i1, i2] and 
			(OverlapI[i2, i3] or
			StartsI[i2,i3]))
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0



// DuringI
check T_DuringI{
	all i1, i2, i3 : Interval {
		(DuringI[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}
		(DuringI[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or 
			DuringI[i1, i3] or
			MeetsI[i1, i3] or
			StartsI[i1, i3]
		}

		(DuringI[i1, i2] and During[i2, i3])
		implies {
			Overlap[i1, i3] or
			OverlapI[i1, i3] or 
			In[i1, i3] or
			Contains[i1, i3] or
			Equal[i1, i3]
		}

		(DuringI[i1, i2] and 
			(DuringI[i2, i3] or 
			StartsI[i2, i3] or
			FinishesI[i2, i3]))
		implies {
			DuringI[i1, i3]
		}

		(DuringI[i1, i2] and 
			(Overlap[i2, i3] or
			Meets[i2, i3] or
			Starts[i2, i3]))
		implies {
			Overlap[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(DuringI[i1, i2] and 
			(OverlapI[i2, i3] or
			MeetsI[i2, i3] or
			FinishesI[i2, i3]))
		implies {
			OverlapI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Overlaps
check T_Overlaps {
	all i1, i2, i3 : Interval {
		(Overlap[i1, i2] and 
			(Before[i2, i3] or
			Meets[i2, i3]))
		implies {
			Before[i1, i3]
		}
	
		(Overlap[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			DuringI[i1, i3] or
			MeetsI[i1, i3] or
			StartsI[i1, i3]
		}

	
		(Overlap[i1, i2] and 
			(During[i2, i3] or
			Finishes[i2, i3]))
		implies {
			Overlap[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}
		
		(Overlap[i1, i2] and DuringI[i2, i3])
		implies {
			Before[i1, i3] or 
			Overlap[i1, i3] or
			Meets[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(Overlap[i1, i2] and 
			(Overlap[i2, i3] or 
			FinishesI[i2, i3]))
		implies {
			Before[i1, i3] or 
			Overlap[i1, i3] or
			Meets[i1, i3]
		}

		(Overlap[i1, i2] and OverlapI[i2, i3])
		implies {
			Overlap[i1, i3] or
			OverlapI[i1, i3] or 
			In[i1, i3] or
			Contains[i1, i3] or
			Equal[i1, i3]
		}

		(Overlap[i1, i2] and MeetsI[i2, i3])
		implies {
			OverlapI[i1, i3] or
			DuringI[i1, i3] or 
			StartsI[i1, i3]
		}

		(Overlap[i1, i2] and Starts[i2, i3])
		implies {
			Overlap[i1, i3]
		}

		(Overlap[i1, i2] and StartsI[i2, i3])
		implies {
			DuringI[i1, i3] or
			FinishesI[i1, i3] or 
			Overlap[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Overlapped-By
check T_Overlapped_By {
	all i1, i2, i3 : Interval {
		(OverlapI[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3] or 
			Meets[i1, i3] or 
			Overlap[i1, i3] or
			DuringI[i1, i3] or 
			FinishesI[i1, i3]
		}
	
		(OverlapI[i1, i2] and 
			(After[i2, i3] or MeetsI[i2, i3]))
		implies {
			After[i1, i3]
		}

		(OverlapI[i1, i2] and 
			(During[i2, i3] or Starts[i2, i3]))
		implies {
			OverlapI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}

		(OverlapI[i1, i2] and DuringI[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}

		(OverlapI[i1, i2] and Overlap[i2, i3])
		implies {
			Overlap[i1, i3] or
			OverlapI[i1, i3] or
			In[i1, i3] or
			Contains[i1, i3] or
			Equal[i1, i3]
		}
		
		(OverlapI[i1, i2] and 
			(OverlapI[i2, i3] or StartsI[i2, i3]))
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3]
		}

		(OverlapI[i1, i2] and 
			(OverlapI[i2, i3] or StartsI[i2, i3]))
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3]
		}

		(OverlapI[i1, i2] and Meets[i2, i3])
		implies {
			Overlap[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(OverlapI[i1, i2] and Finishes[i2, i3])
		implies {
			OverlapI[i1, i3]
		}
		
		(OverlapI[i1, i2] and FinishesI[i2, i3])
		implies {
			OverlapI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0


// Meets
check T_Meets {
	all i1, i2, i3 : Interval {
		(Meets[i1, i2] and 
			(Before[i2, i3] or
			DuringI[i2, i3] or
			Overlap[i2, i3] or
			Meets[i2, i3] or
			FinishesI[i2, i3]))
		implies {
			Before[i1, i3]
		}

		(Meets[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}

		(Meets[i1, i2] and 
			(During[i2, i3] or
			OverlapI[i2, i3] or
			Finishes[i2, i3]))
		implies {
			Overlap[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}

		(Meets[i1, i2] and MeetsI[i2, i3])
		implies {
			Finishes[i1, i3] or
			FinishesI[i1, i3] or
			Equal[i1, i3]
		}

		(Meets[i1, i2] and 
			(Starts[i2, i3] or
			StartsI[i2, i3]))
		implies {
			Meets[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Met-by
check T_Met_By {
	all i1, i2, i3 : Interval {
		(MeetsI[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
 			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(MeetsI[i1, i2] and 
			(After[i2, i3] or 
			DuringI[i2, i3] or
			OverlapI[i2, i3] or
			MeetsI[i2, i3] or
			StartsI[i2, i3]))
		implies {
			After[i1, i3]
		}

		(MeetsI[i1, i2] and 
			(During[i2, i3] or 
			Overlap[i2, i3] or
			Starts[i2, i3]))
		implies {
			OverlapI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}

		(MeetsI[i1, i2] and Meets[i2, i3])
		implies {
			Starts[i1, i3] or
			StartsI[i1, i3] or
			Equal[i1, i3]
		}

		(MeetsI[i1, i2] and 
			(Finishes[i2, i3] or 
			FinishesI[i2, i3]))
		implies {
			MeetsI[i1, i3]
		}

	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Starts
check T_Starts {
	all i1, i2, i3 : Interval {
		(Starts[i1, i2] and 
			(Before[i2, i3] or
			Meets[i2, i3]))
		implies {
			Before[i1, i3]
		}

		(Starts[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3]
		}

		(Starts[i1, i2] and 
			(During[i2, i3] or
			Finishes[i2, i3]))
		implies {
			During[i1, i3]
		}

		(Starts[i1, i2] and DuringI[i2, i3])
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(Starts[i1, i2] and Overlap[i2, i3])
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3]
		}

		(Starts[i1, i2] and OverlapI[i2, i3])
		implies {
			OverlapI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}
	
		(Starts[i1, i2] and MeetsI[i2, i3])
		implies {
			MeetsI[i1, i3]
		}
		
		(Starts[i1, i2] and Starts[i2, i3])
		implies {
			Starts[i1, i3]
		}

		(Starts[i1, i2] and StartsI[i2, i3])
		implies {
			Starts[i1, i3] or
			StartsI[i1, i3] or
			Equal[i1, i3]
		}

		(Starts[i1, i2] and FinishesI[i2, i3])
		implies {
			Before[i1, i3] or
			Meets[i1, i3] or
			Overlap[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Started by
check T_Started_By {
	all i1, i2, i3 : Interval {
		(StartsI[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3] or
			Overlap[i1, i3] or
			Meets[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(StartsI[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3]
		}

		(StartsI[i1, i2] and During[i2, i3])
		implies {
			OverlapI[i1, i3] or
			During[i1, i3] or
			Finishes[i1, i3]
		}

		(StartsI[i1, i2] and 
			(DuringI[i2, i3] or FinishesI[i2, i3]))
		implies {
			DuringI[i1, i3]
		}

		(StartsI[i1, i2] and 
			(Overlap[i2, i3] or Meets[i2, i3]))
		implies {
			Overlap[i1, i3] or
			DuringI[i1, i3] or
			FinishesI[i1, i3]
		}

		(StartsI[i1, i2] and 
			(OverlapI[i2, i3] or Finishes[i2, i3]))
		implies {
			OverlapI[i1, i3]
		}

		(StartsI[i1, i2] and MeetsI[i2, i3])
		implies {
			MeetsI[i1, i3]
		}

		(StartsI[i1, i2] and Starts[i2, i3])
		implies {
			Starts[i1, i3] or
			StartsI[i1, i3] or
			Equal[i1, i3]
		}

		(StartsI[i1, i2] and StartsI[i2, i3])
		implies {
			StartsI[i1, i3]
		}

	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Finishes
check T_Finishes {
	all i1, i2, i3 : Interval {
		(Finishes[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3]
		}

		(Finishes[i1, i2] and 
			(After[i2, i3] or
			MeetsI[i2, i3]))
		implies {
			After[i1, i3]
		}

		(Finishes[i1, i2] and 
			(During[i2, i3] or
			Starts[i2, i3]))
		implies {
			During[i1, i3]
		}

		(Finishes[i1, i2] and DuringI[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}

		(Finishes[i1, i2] and Overlap[i2, i3])
		implies {
			Overlap[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}

		(Finishes[i1, i2] and 
			(OverlapI[i2, i3] or
				StartsI[i2, i3]))
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3]
		}

		(Finishes[i1, i2] and Meets[i2, i3])
		implies {
			Meets[i1, i3]
		}

		(Finishes[i1, i2] and FinishesI[i2, i3])
		implies {
			Finishes[i1, i3] or
			FinishesI[i1, i3] or
			Equal[i1, i3]
		}

	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0

// Finished-by
check T_Finished_By {
	all i1, i2, i3 : Interval {
		(FinishesI[i1, i2] and Before[i2, i3])
		implies {
			Before[i1, i3]
		}

		(FinishesI[i1, i2] and After[i2, i3])
		implies {
			After[i1, i3] or
			OverlapI[i1, i3] or
			MeetsI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}

		(FinishesI[i1, i2] and During[i2, i3])
		implies {
			Overlap[i1, i3] or
			During[i1, i3] or
			Starts[i1, i3]
		}

		(FinishesI[i1, i2] and 
			(DuringI[i2, i3] or
			StartsI[i2, i3]))
		implies {
			DuringI[i1, i3]
		}
		
		(FinishesI[i1, i2] and 
			(Overlap[i2, i3] or
			Starts[i2, i3]))
		implies {
			Overlap[i1, i3]
		}

		(FinishesI[i1, i2] and 
			(OverlapI[i2, i3] or
			MeetsI[i2, i3]))
		implies {
			OverlapI[i1, i3] or
			DuringI[i1, i3] or
			StartsI[i1, i3]
		}

		(FinishesI[i1, i2] and Meets[i2, i3])
		implies {
			Meets[i1, i3]
		}

		(FinishesI[i1, i2] and Finishes[i2, i3])
		implies {
			Finishes[i1, i3] or
			FinishesI[i1, i3] or
			Equal[i1, i3]
		}

		(FinishesI[i1, i2] and FinishesI[i2, i3])
		implies {
			FinishesI[i1, i3]
		}
	}
} for exactly 3 Interval, 6 Boundary, 0 Proposition expect 0


/*
 * Holds Transitivity
 */
check Holds_Transitivity {
	all p : Proposition, i1, i2 : Interval |
		Holds[p, i1] and In[i2, i1] implies Holds[p, i2]
} for exactly 2 Interval, 4 Boundary, exactly 1 Proposition expect 0


/* 
 * Auxiliary Custom checks 
 */
check NotPrecedes{
	all i1, i2 : Interval {
		(not Precedes[i1, i2]) iff (Precedes[i2, i1] or Intersects[i1, i2])
	}
}for 6 expect 0


/*
 *  Runs
 */

// Interval predicate runs
run Equal{
	some i1, i2 : Interval {
		Equal[i1, i2]
	}
} for 4 expect 1

run Before{
	some i1, i2 : Interval {
		Before[i1, i2]
	}
} for 4 expect 1

run Meets{
	some i1, i2 : Interval {
		Meets[i1, i2]
	}
} for 4

run Overlap{
	some i1, i2 : Interval {
		Overlap[i1, i2]
	}
} for 4 expect 1

run During{
	some i1, i2 : Interval {
		During[i1, i2]
	}
} for 4 expect 1
 
run Starts{
	some i1, i2 : Interval {
		Starts[i1, i2]
	}
} for 4 expect 1

run Finishes{
	some i1, i2 : Interval {
		Finishes[i1, i2]
	}
} for 4 expect 1

/*
 Proposition Runs
 */
run Holds{
	some p : Proposition, i : Interval {
		Holds[p, i]
	}
} for 4 expect 1

run Occurs{
	some p : Proposition, i : Interval {
		Occurs[p, i]
	}
} for 4 expect 1

/*
 * Scenarios
 */
// Some interval becomes ongoing
run Simple_Ongoing{
	eventually some Ongoing
} for 4 expect 1

// A singleton interval exists
run Singleton{
	some i : Interval | Singleton[i]
} for 4 expect 1

// Intervals repeat:
//	   No instance should be found (expect 0)
run Repeating_Intervals{
	some i : Interval{
		eventually (Ongoing[i] and 
			eventually (not Ongoing[i] and eventually Ongoing[i]))
	}
} for 6 but 1 Interval expect 0

// Interval during infinite interval
run During_Infinite{
	some i1, i2 : Interval{
		During[i1, i2]
		not Finite[i2]
	}
} for 8 but 2 Interval expect 1
