module ALTLv2

/*
 * Signatures: 
	  - Proposition
      - Boundary
      - Interval

 */

/*
 * Variable Signatures:
       - Happens 
       - Ongoing 
 */ 

// Visualization function to reorder theme priority
fun A_Starting: Interval {
	Starting
}

fun B_Ending : Interval {
	Ending
}

fun C_Ongoing : Interval {
	 Ongoing
}

/* Testing sigs */
sig T extends Interval{}
sig P extends Proposition{}


abstract sig Proposition {}
var sig Active in Proposition {}

sig Boundary {}

abstract sig Interval {
	start : one Boundary, 
	end : lone Boundary,
}

var sig Happens in Boundary {}

var sig Ongoing in Interval {}
var sig Starting, Ending in Ongoing{}


pred Ongoing[ i : Interval ] {
	some i & Ongoing
}

pred Starting[ i : Interval ] {
	some i & Starting
}

pred Ending[ i : Interval ] {
	some i & Ending
}

pred Active[p : Proposition] {
	some p & Active
}

pred Happens[b : Boundary] {
	some b & Happens
}

pred Finite[i : Interval] {
	eventually Ending[i]
}

pred Singleton[i : Interval] {
	eventually (Starting[i] and Ending[i])
}

pred Initial[i : Interval] {
	Starting[i]
}

// Auxiliary Predicate Encoding	
fact { 

	// Ongoing intervals in the next state are those that start and
	// the non-terminating currently ongoing intervals
	always{
		Ongoing' = Ongoing + Starting' - Ending
		Starting = start.Happens
		Ending = end.Happens
	}

	// (1) Initial ongoing intervals are starting
	all i: Interval | Ongoing[i] iff Starting[i]

	// (2) Intervals start if they were previously not ongoing
	all i : Interval | always (i in Starting' implies no i & Ongoing)
	
	// (3) Intervals do not repeat
	all i : Interval | always (Ending[i] implies after always not Starting[i])

}



// Performance Improving Facts
fact {
	// (4) All intervals start
	all i : Interval | eventually Starting[i]

	// (5) All boundaries belong to an interval
	Boundary in Interval.(start+end)
}



/* 
 * Interval predicates
 */

// EQUAL(i1, i2): i1 and i2 are ongoing during the same instants.
pred Equal[i1 : Interval, i2 : Interval] {
	always (Ongoing[i1] iff Ongoing[i2])
}


// BEFORE(i1, i2): time interval i1 is before interval i2,
// and they do not overlap in any way

let strong_release [p1, p2] = {eventually p1 and p1 releases p2}

pred Before[i1 : Interval, i2 : Interval] {
	strong_release[	Ending[i1] , not Ongoing[i2]]
	not eventually (Ending[i1] and after Starting[i2])
}

// MEETS(i1, i2): interval i1 is before interval i2, but there is no interval between them, 
// i.e., i1 ends where i2 starts
pred Meets[i1 : Interval, i2 : Interval] {
	eventually (Ending[i1] and after Starting[i2])
}


// OVERLAP(i1, i2): interval i1 starts before i2, and they overlap
pred Overlap[i1 : Interval, i2 : Interval] {
	Ongoing[i1] releases not Ongoing[i2]
	eventually (Ending[i1] and Ongoing[i2] and not Ending[i2])
}


// DURING(i1, i2): time interval i1 is fully contained within i2
pred During[i1 : Interval, i2 : Interval] {
	always {
		Ongoing[i1] implies Ongoing[i2]		
		Starting[i1] implies not Starting[i2]
	}

	// Infinite intervals are not contained in infinite intervals
	eventually (Ending[i1] and not Ending[i2])
}


// STARTS(i1,i2): time interval i1 shares the same beginning as i2, 
// but ends before i2 ends
pred Starts[i1 : Interval, i2 : Interval] {
	eventually (Starting[i1] and Starting[i2])
	eventually (Ongoing[i2] and not Ongoing[i1])
}

// FINISHES(i1, i2): time interval i1 shares the same end as i2,
// but begins after i2 begins
pred Finishes[i1 : Interval, i2 : Interval] {
	eventually (Ongoing[i2] and not Ongoing[i1])
	always (Ending[i1] iff Ending[i2])
}


/*
 * Proposition predicates
 */
pred Holds[p : Proposition, t : Interval]{
	always (Ongoing[t] implies Active[p])
}

pred Occurs[p : Proposition, t : Interval] {
	eventually (Ongoing[t] and Active[p])
}


/*
 * Additional predicates
 */
pred In[i1 : Interval, i2 : Interval] {
	During[i1, i2] or Starts[i1, i2] or Finishes[i1, i2]
}


pred Contains[i1 : Interval, i2 : Interval] {
	DuringI[i1, i2] or StartsI[i1, i2] or FinishesI[i1, i2]
}

pred Precedes[i1 : Interval, i2 : Interval] {
	Before[i1, i2] or Meets[i1, i2]
}

pred Intersects[i1 : Interval, i2 : Interval] {
	Equal[i1,i2] or In[i1,i2] or In[i2,i1] or Overlap[i1, i2] or Overlap[i2,i1]
}


pred Initiates[i1 : Interval, i2 : Interval] {
	Equal[i1, i2] or In[i2, i1] or Overlap[i1, i2] 
	or Starts[i1, i2] or Starts[i2, i1]
}

pred Complement[I1 : set Interval, I2 : set Interval] {
	always {
		(no i1: I1 | Ongoing[i1]) iff
			(some i2: I2| Ongoing[i2])
	}
}

/*
 *  Inverted predicates
 */
pred After[i1 : Interval, i2: Interval] { Before[i2, i1] }

pred DuringI[i1 : Interval, i2: Interval] { During[i2, i1] }

pred OverlapI[i1 : Interval, i2: Interval] { Overlap[i2, i1] }

pred MeetsI[i1 : Interval, i2: Interval] { Meets[i2, i1] }

pred StartsI[i1 : Interval, i2: Interval] { Starts[i2, i1] }

pred FinishesI[i1 : Interval, i2: Interval] { Finishes[i2, i1] }

/* Predicate Visualization Functions */
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
 * Base Property Check
 */
check Intervals_Dont_Repeat {
	all t : Interval | always {
		Ongoing[t] implies
			always (not Ongoing[t] implies (always not Ongoing[t]))
	}
} for 2 but 1 Interval expect 0


/* 
 * Derived Property Checks
 */

let Exclusion [a, b] = not (a and b)

// Two intervals have at most relation
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


// Two intervals have at least one relation
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
 * Transitivity Properties
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



// Contains
check T_Contains {
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

/* Custom checks */
check NotPrecedes{
	all i1, i2 : Interval {
		(not Precedes[i1, i2]) iff (Precedes[i2, i1] or Intersects[i1, i2])
	}
}for 6	

/* Runs */

run Simple_Ongoing{
	eventually some Ongoing
} for 4 expect 1

run Singleton{
	some i : Interval | Singleton[i]
} for 4


/* Intervals repeat
   No instance should be found (expect 0) */
run Repeating_Intervals{
	some i : Interval{
		eventually (Ongoing[i] and 
			eventually (not Ongoing[i] and eventually Ongoing[i]))
	}
} for 6 but 1 Interval expect 0


run Equal{
	some i1, i2 : Interval {
		Equal[i1, i2]
	}
} for 4

run Before{
	some i1, i2 : Interval {
		Before[i1, i2]
	}
} for 4

run Meets{
	some i1, i2 : Interval {
		Meets[i1, i2]
	}
} for 4

run Overlap{
	some i1, i2 : Interval {
		Overlap[i1, i2]
	}
} for 4

run During{
	some i1, i2 : Interval {
		During[i1, i2]
	}
} for 4
 
run Starts{
	some i1, i2 : Interval {
		Starts[i1, i2]
	}
} for 4

run Finishes{
	some i1, i2 : Interval {
		Finishes[i1, i2]
	}
} for 4

run Holds{
	some p : Proposition, i : Interval {
		Holds[p, i]
	}
} for 4

run Occurs{
	some p : Proposition, i : Interval {
		Occurs[p, i]
	}
} for 4

run During_Infinite{
	some i1, i2 : Interval{
		During[i1, i2]
		not Finite[i2]
	}
} for 8 but 2 Interval
