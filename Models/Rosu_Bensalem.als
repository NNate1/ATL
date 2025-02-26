module Rosu_Bensalem

/* Testing sigs */
sig T extends Interval{}
sig P extends Proposition{}


/*
 * Signatures:
	- Interval:
	- Proposition
 */

/*
 * Variable Signatures: 
       - Ongoing 
 */ 


abstract sig Proposition {}

abstract sig Interval {}

var sig Ongoing in Interval + Proposition {}

pred Ongoing[ t : Interval + Proposition] {
	some t 
	t in Ongoing
}


fact {
	// Intervals must happen
	all t : Interval |
		eventually Ongoing[t]

	// Intervals do not repeat
	all t : Interval {
		not eventually (Ongoing[t] and 
			eventually (not Ongoing[t] and 
				eventually Ongoing[t]))
	}
}

check Intervals_Dont_Repeat {
	all t : Interval | always {
		Ongoing[t] implies 
			always (not Ongoing[t] implies 
				(always not Ongoing[t]))
	}
} for 4 but 0 Proposition

/*
 * Visualization functions
 */
// Starting interval
fun Starting : Interval + Proposition {
	 {t : Interval + Proposition | Ongoing[t] and not before Ongoing[t]}
}

// Terminating interval
fun Terminating : Interval + Proposition {
	 {t : Interval + Proposition | Ongoing[t] and after not Ongoing[t] }
}

// Ongoing Interval
fun Ongoing_Visual : Interval + Proposition{
	{t : Interval + Proposition | t in Ongoing - Starting - Terminating }
}

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
 * Interval predicates
 */

// DURING(t1, t2): time interval t1 is fully contained within t2
pred During[t1 : Interval, t2 : Interval] {
	eventually (Ongoing[t2] and not Ongoing[t1] and 
		eventually (Ongoing[t2] and Ongoing[t1] and 
			eventually (Ongoing[t2]and not Ongoing[t1])))
}


// STARTS(t1,t2): time interval t1 shares the same beginning as t2, 
// but ends before t2 ends
pred Starts[t1 : Interval, t2 : Interval] {
	always (Ongoing[t1] implies Ongoing[t2])
	not eventually (Ongoing[t2] and not Ongoing[t1] and
		eventually Ongoing[t1])
	eventually (Ongoing[t2] and not Ongoing[t1])
}


// FINISHES(t1, t2): time interval t1 shares the same end as t2,
// but begins after t2 begins
pred Finishes[t1 : Interval, t2 : Interval] {
	always (Ongoing[t1] implies Ongoing[t2])
	eventually (Ongoing[t2] and not Ongoing[t1])
	not eventually (Ongoing[t2] and Ongoing[t1] and 
		eventually (Ongoing[t2] and not Ongoing[t1]))
}


// BEFORE(t1, t2): time interval t1 is before interval t2,
// and they do not overlap in any way
pred Before[t1 : Interval, t2 : Interval] {
	eventually (Ongoing[t1] and 
		eventually (not Ongoing[t1] and not Ongoing[t2] and 
			eventually Ongoing[t2]))
}


// OVERLAP(t1, t2): interval t1 starts before t2, and they overlap
pred Overlap[t1 : Interval, t2 : Interval] {
	eventually (Ongoing[t1] and not Ongoing[t2] and 
		eventually ( Ongoing[t1] and Ongoing[t2] and
			eventually (not Ongoing[t1] and Ongoing[t2])))
}


// MEETS(t1, t2): interval t1 is before interval t2, but there is no interval between them, 
// i.e. t1 ends where t2 starts
pred Meets[t1 : Interval, t2 : Interval] {
	eventually (Ongoing[t1] and (eventually Ongoing[t2]) and
		not eventually (Ongoing[t1] and Ongoing[t2]) and
		not eventually (not Ongoing[t1] and not Ongoing[t2] and 
			eventually Ongoing[t2]))
}


// EQUAL(t1, t2): t1 and t2 are the same interval.
pred Equal[t1 : Interval, t2 : Interval] {
	always (Ongoing[t1] iff Ongoing[t2])
}

/*
 * Auxiliary interval predicates 
 */

// IN(t1, t2): interval t1 is wholly contained in t2
pred In[t1 : Interval, t2 : Interval] {
	During[t1, t2] or Starts[t1, t2] or Finishes[t1, t2]
}

// Contained(t1, t2): interval t1 contains t2
pred Contains[t1 : Interval, t2 : Interval] {
	DuringI[t1, t2] or StartsI[t1, t2] or FinishesI[t1, t2]
}

/* Inverted Predicates */
pred After[t1 : Interval, t2: Interval] { Before[t2, t1] }

pred DuringI[t1 : Interval, t2: Interval] { During[t2, t1] }

pred OverlapI[t1 : Interval, t2: Interval] { Overlap[t2, t1] }

pred MeetsI[t1 : Interval, t2: Interval] { Meets[t2, t1] }

pred StartsI[t1 : Interval, t2: Interval] { Starts[t2, t1] }

pred FinishesI[t1 : Interval, t2: Interval] { Finishes[t2, t1] }

/* Additional Predicates */
pred Initial[interval : Interval ] {
	Ongoing[interval]
}

pred Terminates[interval: Interval] {
	eventually (Ongoing[interval] and eventually not Ongoing[interval])
}

pred Precedes[t1, t2 : Interval] {
	Before[t1, t2] or Meets[t1, t2]
}

pred Initiates[t1, t2 : Interval] {
	In[t2, t1] or Overlap[t1, t2] or Equal[t1, t2]
}

pred Global[t : Interval] {
	always Ongoing[t]
}

pred Complement[T1 : set Interval, T2 : set Interval]{
	always {
		(no t1: T1| Ongoing[t1]) iff
			(some t2: T2| Ongoing[t2])
	}
}

pred Singleton [t : Interval] {
	always (t in Ongoing implies t not in Ongoing')
}


/*
 * Proposition predicates
 */

pred Holds[p : Proposition, t : Interval]{
	always (Ongoing[t] implies Ongoing[p])
}

pred Occurs[p : Proposition, t : Interval] {
	eventually (Ongoing[t] and Ongoing[p])
}


/* 
 * Axioms and checks
 */

let Exclusion [a, b] = not (a and b)

// Two intervals only share one relation
check Exclusivity {
	all t1, t2 : Interval {
		Exclusion[Starts[t1, t2], During[t1, t2]]

		Exclusion[Finishes[t1, t2], During[t1, t2]]
		Exclusion[Finishes[t1, t2], Starts[t1, t2]]

		Exclusion[Before[t1, t2], During[t1, t2]]
		Exclusion[Before[t1, t2], Starts[t1, t2]]
		Exclusion[Before[t1, t2], Finishes[t1, t2]]

		Exclusion[Overlap[t1, t2], During[t1, t2]]
		Exclusion[Overlap[t1, t2], Starts[t1, t2]]
		Exclusion[Overlap[t1, t2], Finishes[t1, t2]]
		Exclusion[Overlap[t1, t2], Before[t1, t2]]

		Exclusion[Meets[t1, t2], During[t1, t2]]
		Exclusion[Meets[t1, t2], Starts[t1, t2]]
		Exclusion[Meets[t1, t2], Finishes[t1, t2]]
		Exclusion[Meets[t1, t2], Before[t1, t2]]
		Exclusion[Meets[t1, t2], Overlap[t1, t2]]


		Exclusion[Equal[t1, t2], During[t1, t2]]
		Exclusion[Equal[t1, t2], Starts[t1, t2]]
		Exclusion[Equal[t1, t2], Finishes[t1, t2]]
		Exclusion[Equal[t1, t2], Before[t1, t2]]
		Exclusion[Equal[t1, t2], Overlap[t1, t2]]
		Exclusion[Equal[t1, t2], Meets[t1, t2]]
	}
--} for 4 but 2 Interval--OK
} for 2 Interval, 0 Proposition

// Two intervals must have one relation
check MinimumRelation{
	all t1, t2 : Interval {
		(
		During[t1, t2] or During[t2, t1]
		or
		Starts[t1, t2] or Starts[t2, t1]
		or
		Finishes[t1, t2] or Finishes[t2, t1]
		or
		Before[t1, t2] or Before[t2, t1]
		or
		Overlap[t1, t2] or Overlap[t2, t1]
		or
		Meets[t1, t2] or Meets[t2, t1]
		or
		Equal[t1,t2]
		)
	}
--} for 4 but 2 Interval -- OK
} for 2 Interval, 0 Proposition

/*
 * Transitivity Properties
 */
// Before
check T_Before {
	all t1, t2, t3 : Interval {
		(Before[t1, t2] and 
			(During[t2, t3] or 
			OverlapI[t2, t2] or 
			MeetsI[t2, t2] or 	
			Finishes[t2, t3]))
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}

		(Before[t1, t2] and 
			(Before[t2, t3] or 
			DuringI[t2, t3] or 
			Overlap[t2, t3] or 	
			Meets[t2, t3] or 
			Starts[t2, t3] or 
			StartsI[t2, t3] or 
			FinishesI[t2, t3]))
		implies {
			Before[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// After
check T_After {
	all t1, t2, t3 : Interval {
		(After[t1, t2] and 
			(During[t2, t3] or 
			Overlap[t2, t3] or 
			Meets[t2, t3] or 	
			Starts[t2, t3] or 	
			Finishes[t2, t3]))
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}

		(After[t1, t2] and 
			(After[t2, t3] or 
			DuringI[t2, t3] or 
			OverlapI[t2, t3] or 	
			MeetsI[t2, t3] or 
			StartsI[t2, t3] or 
			Finishes[t2, t3] or
			FinishesI[t2, t3]))
		implies {
			After[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// During
check T_During {
	all t1, t2, t3 : Interval {
		(During[t1, t2] and 
			(Before[t2, t3] or 
			Meets[t2, t3]))
		implies {
			Before[t1, t3]
		}

		(During[t1, t2] and 
			(After[t2, t3] or 
			MeetsI[t2,t3]))
		implies {
			After[t1, t3]
		}

		(During[t1, t2] and 
			(During[t2, t3] or 
			Starts[t2,t3] or
			Finishes[t2,t3]))
		implies {
			During[t1, t3]
		}

		(During[t1, t2] and 
			(Overlap[t2, t3] or
			FinishesI[t2,t3]))
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}

		(During[t1, t2] and 
			(OverlapI[t2, t3] or
			StartsI[t2,t3]))
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}
	}
-- } for 6 but 3 Interval // 4376ms, 1385
--} for 3 Interval, 0 Proposition // 3619ms, 1101ms
} for exactly 3 Interval, 0 Proposition // 3739ms, 1353ms

// Contains
check T_Contains {
	all t1, t2, t3 : Interval {
		(DuringI[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}
		(DuringI[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or 
			DuringI[t1, t3] or
			MeetsI[t1, t3] or
			StartsI[t1, t3]
		}

		(DuringI[t1, t2] and During[t2, t3])
		implies {
			Overlap[t1, t3] or
			OverlapI[t1, t3] or 
			In[t1, t3] or
			Contains[t1, t3] or
			Equal[t1, t3]
		}

		(DuringI[t1, t2] and 
			(DuringI[t2, t3] or 
			StartsI[t2, t3] or
			FinishesI[t2, t3]))
		implies {
			DuringI[t1, t3]
		}

		(DuringI[t1, t2] and 
			(Overlap[t2, t3] or
			Meets[t2, t3] or
			Starts[t2, t3]))
		implies {
			Overlap[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(DuringI[t1, t2] and 
			(OverlapI[t2, t3] or
			MeetsI[t2, t3] or
			FinishesI[t2, t3]))
		implies {
			OverlapI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// Overlaps
check T_Overlaps {
	all t1, t2, t3 : Interval {
		(Overlap[t1, t2] and 
			(Before[t2, t3] or
			Meets[t2, t3]))
		implies {
			Before[t1, t3]
		}
	
		(Overlap[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			DuringI[t1, t3] or
			MeetsI[t1, t3] or
			StartsI[t1, t3]
		}

	
		(Overlap[t1, t2] and 
			(During[t2, t3] or
			Finishes[t2, t3]))
		implies {
			Overlap[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}
		
		(Overlap[t1, t2] and DuringI[t2, t3])
		implies {
			Before[t1, t3] or 
			Overlap[t1, t3] or
			Meets[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(Overlap[t1, t2] and 
			(Overlap[t2, t3] or 
			FinishesI[t2, t3]))
		implies {
			Before[t1, t3] or 
			Overlap[t1, t3] or
			Meets[t1, t3]
		}

		(Overlap[t1, t2] and OverlapI[t2, t3])
		implies {
			Overlap[t1, t3] or
			OverlapI[t1, t3] or 
			In[t1, t3] or
			Contains[t1, t3] or
			Equal[t1, t3]
		}

		(Overlap[t1, t2] and MeetsI[t2, t3])
		implies {
			OverlapI[t1, t3] or
			DuringI[t1, t3] or 
			StartsI[t1, t3]
		}

		(Overlap[t1, t2] and Starts[t2, t3])
		implies {
			Overlap[t1, t3]
		}

		(Overlap[t1, t2] and StartsI[t2, t3])
		implies {
			DuringI[t1, t3] or
			FinishesI[t1, t3] or 
			Overlap[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// Overlapped-By
check T_Overlapped_By {
	all t1, t2, t3 : Interval {
		(OverlapI[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3] or 
			Meets[t1, t3] or 
			Overlap[t1, t3] or
			DuringI[t1, t3] or 
			FinishesI[t1, t3]
		}
	
		(OverlapI[t1, t2] and 
			(After[t2, t3] or MeetsI[t2, t3]))
		implies {
			After[t1, t3]
		}

		(OverlapI[t1, t2] and 
			(During[t2, t3] or Starts[t2, t3]))
		implies {
			OverlapI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}

		(OverlapI[t1, t2] and DuringI[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}

		(OverlapI[t1, t2] and Overlap[t2, t3])
		implies {
			Overlap[t1, t3] or
			OverlapI[t1, t3] or
			In[t1, t3] or
			Contains[t1, t3] or
			Equal[t1, t3]
		}
		
		(OverlapI[t1, t2] and 
			(OverlapI[t2, t3] or StartsI[t2, t3]))
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3]
		}

		(OverlapI[t1, t2] and 
			(OverlapI[t2, t3] or StartsI[t2, t3]))
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3]
		}

		(OverlapI[t1, t2] and Meets[t2, t3])
		implies {
			Overlap[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(OverlapI[t1, t2] and Finishes[t2, t3])
		implies {
			OverlapI[t1, t3]
		}
		
		(OverlapI[t1, t2] and FinishesI[t2, t3])
		implies {
			OverlapI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}
	}

} for 3 Interval, 0 Proposition


// Meets
check T_Meets {
	all t1, t2, t3 : Interval {
		(Meets[t1, t2] and 
			(Before[t2, t3] or
			DuringI[t2, t3] or
			Overlap[t2, t3] or
			Meets[t2, t3] or
			FinishesI[t2, t3]))
		implies {
			Before[t1, t3]
		}

		(Meets[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}

		(Meets[t1, t2] and 
			(During[t2, t3] or
			OverlapI[t2, t3] or
			Finishes[t2, t3]))
		implies {
			Overlap[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}

		(Meets[t1, t2] and MeetsI[t2, t3])
		implies {
			Finishes[t1, t3] or
			FinishesI[t1, t3] or
			Equal[t1, t3]
		}

		(Meets[t1, t2] and 
			(Starts[t2, t3] or
			StartsI[t2, t3]))
		implies {
			Meets[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// Met-by
check T_Met_By {
	all t1, t2, t3 : Interval {
		(MeetsI[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
 			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(MeetsI[t1, t2] and 
			(After[t2, t3] or 
			DuringI[t2, t3] or
			OverlapI[t2, t3] or
			MeetsI[t2, t3] or
			StartsI[t2, t3]))
		implies {
			After[t1, t3]
		}

		(MeetsI[t1, t2] and 
			(During[t2, t3] or 
			Overlap[t2, t3] or
			Starts[t2, t3]))
		implies {
			OverlapI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}

		(MeetsI[t1, t2] and Meets[t2, t3])
		implies {
			Starts[t1, t3] or
			StartsI[t1, t3] or
			Equal[t1, t3]
		}

		(MeetsI[t1, t2] and 
			(Finishes[t2, t3] or 
			FinishesI[t2, t3]))
		implies {
			MeetsI[t1, t3]
		}

	}
} for 3 Interval, 0 Proposition

// Starts
check T_Starts {
	all t1, t2, t3 : Interval {
		(Starts[t1, t2] and 
			(Before[t2, t3] or
			Meets[t2, t3]))
		implies {
			Before[t1, t3]
		}

		(Starts[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3]
		}

		(Starts[t1, t2] and 
			(During[t2, t3] or
			Finishes[t2, t3]))
		implies {
			During[t1, t3]
		}

		(Starts[t1, t2] and DuringI[t2, t3])
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(Starts[t1, t2] and Overlap[t2, t3])
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3]
		}

		(Starts[t1, t2] and OverlapI[t2, t3])
		implies {
			OverlapI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}
	
		(Starts[t1, t2] and MeetsI[t2, t3])
		implies {
			MeetsI[t1, t3]
		}
		
		(Starts[t1, t2] and Starts[t2, t3])
		implies {
			Starts[t1, t3]
		}

		(Starts[t1, t2] and StartsI[t2, t3])
		implies {
			Starts[t1, t3] or
			StartsI[t1, t3] or
			Equal[t1, t3]
		}

		(Starts[t1, t2] and FinishesI[t2, t3])
		implies {
			Before[t1, t3] or
			Meets[t1, t3] or
			Overlap[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

// Started by
check T_Started_By {
	all t1, t2, t3 : Interval {
		(StartsI[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3] or
			Overlap[t1, t3] or
			Meets[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(StartsI[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3]
		}

		(StartsI[t1, t2] and During[t2, t3])
		implies {
			OverlapI[t1, t3] or
			During[t1, t3] or
			Finishes[t1, t3]
		}

		(StartsI[t1, t2] and 
			(DuringI[t2, t3] or FinishesI[t2, t3]))
		implies {
			DuringI[t1, t3]
		}

		(StartsI[t1, t2] and 
			(Overlap[t2, t3] or Meets[t2, t3]))
		implies {
			Overlap[t1, t3] or
			DuringI[t1, t3] or
			FinishesI[t1, t3]
		}

		(StartsI[t1, t2] and 
			(OverlapI[t2, t3] or Finishes[t2, t3]))
		implies {
			OverlapI[t1, t3]
		}

		(StartsI[t1, t2] and MeetsI[t2, t3])
		implies {
			MeetsI[t1, t3]
		}

		(StartsI[t1, t2] and Starts[t2, t3])
		implies {
			Starts[t1, t3] or
			StartsI[t1, t3] or
			Equal[t1, t3]
		}

		(StartsI[t1, t2] and StartsI[t2, t3])
		implies {
			StartsI[t1, t3]
		}

	}
} for 3 Interval, 0 Proposition

// Finishes
check T_Finishes {
	all t1, t2, t3 : Interval {
		(Finishes[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3]
		}

		(Finishes[t1, t2] and 
			(After[t2, t3] or
			MeetsI[t2, t3]))
		implies {
			After[t1, t3]
		}

		(Finishes[t1, t2] and 
			(During[t2, t3] or
			Starts[t2, t3]))
		implies {
			During[t1, t3]
		}

		(Finishes[t1, t2] and DuringI[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}

		(Finishes[t1, t2] and Overlap[t2, t3])
		implies {
			Overlap[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}

		(Finishes[t1, t2] and 
			(OverlapI[t2, t3] or
				StartsI[t2, t3]))
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3]
		}

		(Finishes[t1, t2] and Meets[t2, t3])
		implies {
			Meets[t1, t3]
		}

		(Finishes[t1, t2] and FinishesI[t2, t3])
		implies {
			Finishes[t1, t3] or
			FinishesI[t1, t3] or
			Equal[t1, t3]
		}

	}
} for 3 Interval, 0 Proposition

// Finished-by
check T_Finished_By {
	all t1, t2, t3 : Interval {
		(FinishesI[t1, t2] and Before[t2, t3])
		implies {
			Before[t1, t3]
		}

		(FinishesI[t1, t2] and After[t2, t3])
		implies {
			After[t1, t3] or
			OverlapI[t1, t3] or
			MeetsI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}

		(FinishesI[t1, t2] and During[t2, t3])
		implies {
			Overlap[t1, t3] or
			During[t1, t3] or
			Starts[t1, t3]
		}

		(FinishesI[t1, t2] and 
			(DuringI[t2, t3] or
			StartsI[t2, t3]))
		implies {
			DuringI[t1, t3]
		}
		
		(FinishesI[t1, t2] and 
			(Overlap[t2, t3] or
			Starts[t2, t3]))
		implies {
			Overlap[t1, t3]
		}

		(FinishesI[t1, t2] and 
			(OverlapI[t2, t3] or
			MeetsI[t2, t3]))
		implies {
			OverlapI[t1, t3] or
			DuringI[t1, t3] or
			StartsI[t1, t3]
		}

		(FinishesI[t1, t2] and Meets[t2, t3])
		implies {
			Meets[t1, t3]
		}

		(FinishesI[t1, t2] and Finishes[t2, t3])
		implies {
			Finishes[t1, t3] or
			FinishesI[t1, t3] or
			Equal[t1, t3]
		}

		(FinishesI[t1, t2] and FinishesI[t2, t3])
		implies {
			FinishesI[t1, t3]
		}
	}
} for 3 Interval, 0 Proposition

/*
 * Holds Properties
 */

// H.1: If a property p holds over an interval T, it holds over all subintervals of T
check Holds_Transitivity {
	all p : Proposition, T, t : Interval |
		Holds[p, T] and In[t, T] implies Holds[p, t]
} for 6 but 2 Interval --OK

/*
 * Runs
 */

run Interval {
	#Interval = 2
} for 4

run Ongoing {
	some Ongoing
} for 4

run Ongoing {
	some t : Interval {
		Ongoing[t]; Ongoing[t]; Ongoing[t]; not Ongoing[t]
	}
} for 4

run Proposition {
	eventually some Ongoing & Proposition
} for 4

// Predicate runs

run During{
	some t1, t2 : Interval {
		During[t1, t2]
	}
} for 4
 
run Starts{
	some t1, t2 : Interval {
		Starts[t1, t2]
	}
} for 4

run Finishes{
	some t1, t2 : Interval {
		Finishes[t1, t2]
	}
} for 4

run Before{
	some t1, t2 : Interval {
		Before[t1, t2]
	}
} for 4

run Overlap{
	some t1, t2 : Interval {
		Overlap[t1, t2]
	}
} for 4

run Meets{
	some t1, t2 : Interval {
		Meets[t1, t2]
	}
} for 4

run Equal{
	some t1, t2 : Interval {
		Equal[t1, t2]
	}
} for 4

/* Proposition Runs */

run Holds{
	some p : Proposition, t : Interval {
		Holds[p, t]
	}
} for 6

run Occurs{
	some p : Proposition, t : Interval {
		Occurs[p, t]
	}
} for 4



run Singleton{
	some t : Interval | Singleton[t]
} for 1
