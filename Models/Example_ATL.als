open ATL

// Ignore library test signatures
fact {
	no T
	no P
}


// Starting interval visualization priority
fun Starting : Interval {
	 ATL/Starting
}


/* 
 Message Exchange Protocol with Leader Election

 - Unicast messages
 - Messages that are received preserve sending order
 - At most one message sent per instante
 - Messages as intervals:
	-- Start of interval represents the sending of the message
	-- Ending of interval represents the receival of the message


 - Election dictacte the leader
 - Only the leader can send messages
 - All elections terminate
 - Elections do not intersect
 - Messages are not sent during elections

 - Failed members:
	-- Cannot receive or send messages
    -- Cannot be elected
*/


/*
 * Sigs:
 * - Participant
 * - Message
 * - Leader
 * - Fail
 */

sig Participant {}


sig Message extends Interval {
	sender: one Participant, 
	receiver: one (Participant - sender)
} { not Singleton[this] }

sig Election extends Interval {
	leader : one Participant
} { not Singleton[this] }

sig Fail extends Interval {
	node : one Participant,
} -- { Singleton[this]}

fact { all f : Fail | Singleton[f]}


/*
 * Facts
 */

// Generic message rules
check NoSelfMessaging{
	// Participants do not send messages to themselves
	no (sender & receiver)
} for 6 expect 0


// Message rules
fact {

	// P.1: Only one message can be sent at a time
	no disj m1, m2 : Message | Starts[m1, m2] or Equal[m1, m2]

	 // P.2: Messages are received in the same order as they were sent
	all m1, m2: Message {
		(Finite[m1] and Finite[m2]) implies 
			(not During[m1, m2] and not Finishes[m1, m2])

	}
}


// Leader message rules
fact {
	// Only the last elected leader can send messages
	all m : Message | 
		some election1 : leader.(m.sender) {
		Before[election1, m] or Meets[election1, m]
		no election2 : (Election - election1){
			Before[election2, m] or Meets[election2, m]
			Before[election1, election2] or Meets[election1, election2]
		}
	}
	
}


// Election rules
fact {
	// Messages are not sent during elections
	all e: Election, m : Message {
		not In[m, e]
		not Starts[e, m]
		not Overlap[e, m]
		not Equal[e, m]
	}

	// All elections terminate
	all e : Election | Finite[e]

	// non overlapping elections
	no e1, e2 : Election {
		In[e1, e2] 
		or Overlap[e1, e2]
		or e1 != e2 and Equal[e1, e2]
	}
}


// Current Leader function for visualization
fun Leader : Participant {
	 {p : Participant |
		one election1 : leader.p {
			(no election2 : (Election - election1) |
				Happens[election2.end])
			since
			Happens[election1.end]
		}
	}
}




// Fail rules
fact {
	// failed nodes cannot send messages
	all m : Message, f : Fail {
		f.node = m.sender implies {
			Precedes[m, f] or During[f, m] or Finishes[f, m]
		}
	}

	// failed nodes cannot receive messages
	all m : Message, f : Fail {
		(f.node = m.receiver and Finite[m]) implies Precedes[m, f]
	}

	// failed nodes are not elected
	all e : Election, f : Fail {
		f.node =  e.leader implies Precedes[e, f]
	}

	// failed nodes cannot fail again
	all disj f1, f2 : Fail {
		f1.node != f2.node
	}
}


/*
 * Checks
 */

// Participants that are never leaders never send messages
check NonLeader_Message{
	all p : Participant {
		(no leader.p)
		implies
		(no sender.p)
	}
} for 8 expect 0 -- Ok

// Participants that are never leaders never send messages
check Incorrect_NonLeader_Message{ 
	no	(Message.sender & (Participant - Election.leader))
} for 8 expect 0 -- OK


// Messages are received in the same order as they were sent
check Arrival_Order{
	all disj m1, m2: Message {	
		Finite[m1] implies
		(Overlap[m1, m2] or Before[m1, m2] or Meets[m1, m2] or
		Overlap[m2, m1] or Before[m2, m1] or Meets[m2, m1] or
		not Finite[m2])
		
	}
} for 8 but 3 Message  expect 0-- OK


// If a node fails then it cannot receive messages
check Failed_Receiver {
	all m : Message, f : Fail{
		(m.receiver = f.node and  Precedes[f, m]) implies not Finite[m]
	}
} for 8 expect 0-- OK



// Messages are not sent during elections
check Message_During_Election{
	always no m : Message, e : Election {
		Happens[m.start]
		Ongoing[e]
		not Happens[e.end]
	}
}for 6 but 3 Message, 3 Election expect 0-- OK

// Messages sent requires a previous election
check Message_Implies_Election{
	all m : Message |
		some e : Election {
			m.sender = e.leader
			Precedes[e, m]
		}
}for 6 but 3 Message, 3 Election expect 0-- OK



/*
 * Runs
 */
run Simple_Message{
	some Message
} for 10 but exactly 2 Election expect 1

run Fail {
	some Fail
} for 4 expect 1

run Overlapping_Message{
	some m1, m2 : Message {
		Overlap[m1, m2]
	}
} for 8 expect 1

run Overlapping_Message_Fail{
	some m1, m2 : Message {
		Overlap[m1, m2]
		--Fail.node = m2.receiver
	}
} for 8 but 2 Participant, 2 Message, 1 Election, 1 Fail expect 1

run Fail_After_Sending{
	some f : Fail, m : Message {
		Precedes[m, f]
		f.node = m.sender
	}
} for 8 but 2 Message, 1 Election, 2 Participant, 1 Fail expect 1


run Overlapping_Terminating_Message{
	some m1, m2 : Message {
		Overlap[m1, m2]
		Finite[m2]
	}
} for 8 but exactly 2 Message, exactly 1 Election expect 1

run Multiple_Messages{
	some disj m1, m2: Message {
		m1.sender != m2.sender
	}

} for 10 but exactly 2 Election expect 1

run Multiple_Leaders{
	some el1, el2 : Election {
		el1.leader != el2.leader
	}
} for 6 expect 1

run Multiple_Elections_Single_Leader{
	one p : Participant | all e : Election {
		e.leader = p
	}
} for 6 but 2 Election expect 1

run Fail{
	some p : Participant {
		eventually some node.p.start & Happens
		eventually some leader.p.start & Happens
	}
} for 4 expect 1
