open util/ordering[State] as SO

sig Data {}
sig Checksum {}

one sig Check {
	sums: Data -> Checksum
}

fact {all d: Data | some c: Checksum | d = Check.sums.c and d.(Check.sums) = c}

abstract sig SequenceNumber {}

one sig Number0, Number1 extends SequenceNumber {}

sig Packet {
	data: Data,
	checksum: Checksum,
	sequenceNumber: SequenceNumber
}

//fact {	NAK.data = NAKData and NAK.checksum = NAKData.(Check.sums) and
//		ACK.data = ACKData and ACK.checksum = ACKData.(Check.sums)
//}

// Guarantees Packets will be uncorrupted, for testing
//fact {all p: Packet | p.data = Check.sums.(p.checksum) and (p.data).(Check.sums) = p.checksum}

one sig NAK, ACK extends Packet {}

abstract sig StateMarker {}

one sig Call0FromAbove, Call1FromAbove, Wait0ACKNAK, Wait1ACKNAK, Call0FromBelow, Call1FromBelow extends StateMarker {}

sig State {
	sendBuffer: set Data,
	recvBuffer: set Data,

	lastSent: Packet, // Packet last sent by sender
	currentPacket: Packet, // Packet currently being sent

	currentState: StateMarker, // Current state
//	prevState: StateMarker // Previous State
}


pred State.Init[] {
	this.currentState = Call0FromAbove
	//this.sendBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
	this.sendBuffer = Data
	#this.recvBuffer = 0
	//NAK = p: Packet | p.checksum = (p.data).(Check.sums)
	//this.lastSent = NAK
	NAK.checksum = (NAK.data).(Check.sums)
	ACK.checksum = (ACK.data).(Check.sums)
}

run Init for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred State.End[] {
	#this.sendBuffer = 0
	//this.recvBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
	this.recvBuffer = Data
}

run End for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred Step[s, s': State] {
	s.currentState = Call0FromAbove implies Send[s, s', Number0]
	else s.currentState = Call1FromAbove  implies Send[s, s', Number1]
	else s.currentState = Call0FromBelow implies Recv[s, s', Number0]
	else s.currentState = Call1FromBelow implies Recv[s, s', Number1]
	else s.currentState = Wait0ACKNAK implies ResendIfNecessary[s, s', Number0]
	else s.currentState = Wait1ACKNAK implies ResendIfNecessary[s, s', Number1]
	//else s.currentState = Garble implies GarbleData[s, s']
}

run Step for exactly 5 Packet, exactly 3 Data, exactly 3 Checksum, exactly 2 State
run Step for exactly 2 State, exactly 6 Packet, exactly 4 Data, exactly 4 Checksum

//fun GarbleData[p: Packet]: one Packet {
	//{p': Packet | some d: Data - p.data | p'.data = d and p'.checksum = p.checksum}
//}

//run {
//	some p: Packet | not GarbleData[p].data = p.data
//}

fun MakePacket[d: Data, c: Checksum] : one Packet {
	//{p: Packet | p.data = d and p.checksum = c}
	{p: Packet | p.data = d and p.checksum = c}
}

run MakePacket for exactly 1 Packet, exactly 2 Data, exactly 2 Checksum, exactly 2 State

fun Sum[d: Data] : one Checksum {
	d.(Check.sums)
}

//run {
//	some d: Data | 
//}

pred Send[s, s': State, num: SequenceNumber] {
	one d: s.sendBuffer |
		let c = d.(Check.sums) | 
		let p = {p: Packet - NAK - ACK | p.data = d and p.checksum = c and p.sequenceNumber = num} |
		s'.sendBuffer = s.sendBuffer - d and
		s'.lastSent = p and
		s'.currentPacket.checksum = p.checksum and
		s'.currentPacket.sequenceNumber = p.sequenceNumber and 
		(some d: Data | s'.currentPacket.data = d) and // This is supposed to garble data, but doesn't do it the way we want to
		s'.recvBuffer = s.recvBuffer and
		(num = Number0 implies s'.currentState = Call0FromBelow
		else num = Number1 implies s'.currentState = Call1FromBelow)
		//s'.currentState = Garble and
		//s'.prevState = s.currentState
}

run Send for exactly 2 State, exactly 3 Packet, exactly 1 Data, exactly 3 Checksum

pred Recv[s, s': State, num: SequenceNumber] {
	s'.sendBuffer = s.sendBuffer and
	s'.lastSent = s.lastSent and
	(isUncorrupt[s.currentPacket] and s.currentPacket.sequenceNumber = num implies
		s'.recvBuffer = s.recvBuffer + s.currentPacket.data and
		s'.currentPacket = ACK
	else isUncorrupt[s.currentPacket] and s.currentPacket.sequenceNumber in (SequenceNumber - num) implies
		s'.recvBuffer = s.recvBuffer and
		s'.currentPacket = ACK
	else isCorrupt[s.currentPacket] implies
		s'.recvBuffer = s.recvBuffer and
		s'.currentPacket = NAK) and
	(num = Number0 implies s'.currentState = Wait0ACKNAK
	else num = Number1 implies s'.currentState = Wait1ACKNAK)
	//s'.currentState = Garble
	//s'.prevState = s.currentState
}

run Recv for exactly 2 State, exactly 3 Packet, exactly 3 Data, exactly 3 Checksum

pred ResendIfNecessary[s, s': State, num: SequenceNumber] {
	s'.lastSent = s.lastSent and
	s'.sendBuffer = s.sendBuffer and
	s'.recvBuffer = s.recvBuffer and
	(isNAK[s.currentPacket] or isCorrupt[s.currentPacket] implies
		s'.currentPacket = s.lastSent and
		(num = Number0 implies s'.currentState = Call0FromBelow
		else num = Number1 implies s'.currentState = Call1FromBelow)
		//s'.currentState = Garble and
		//s'.prevState = s.currentState
	else isACK[s.currentPacket] and isUncorrupt[s.currentPacket] implies
		s'.currentPacket = s.currentPacket and
		(num = Number0 implies s'.currentState = Call1FromAbove
		else num = Number1 implies s'.currentState = Call0FromAbove))// and
		//s'.prevState = s.currentState)
}

pred isCorrupt[p: Packet] {
	p.checksum != (p.data).(Check.sums)
}

pred isUncorrupt[p: Packet] {
	p.checksum = (p.data).(Check.sums)
}

pred isNAK[p: Packet] {
	p = NAK
}

pred isACK[p: Packet] {
	p = ACK
}

assert AlwaysUncorrupt {
	all p: Packet | isUncorrupt[p]
}

run isUncorrupt for exactly 2 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State

check AlwaysUncorrupt for exactly 2 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State

//pred GarbleData[s, s': State] { // This is also supposed to garble data when things get sent, but doesn't.
//	s'.sendBuffer = s.sendBuffer
//	s'.recvBuffer = s.recvBuffer
//	s'.lastSent = s.lastSent
//	s'.currentPacket.checksum = s.currentPacket.checksum
//	s'.currentPacket.sequenceNumber = s.currentPacket.sequenceNumber
//	(s.prevState = Call0FromAbove implies s'.currentState = Call0FromBelow
//	else s.prevState = Call1FromAbove implies s'.currentState = Call1FromBelow
//	else s.prevState = Call0FromBelow implies s'.currentState = Wait0ACKNAK
//	else s.prevState = Call1FromBelow implies s'.currentState = Wait1ACKNAK
//	else s.prevState = Wait0ACKNAK implies s'.currentState = Call0FromBelow
//	else s.prevState = Wait1ACKNAK implies s'.currentState = Call1FromBelow)
//	s'.prevState = s.currentState
//	one d: Data - s.currentPacket.data | let choices = d + s.currentPacket.data | one newdata: choices |
//		s'.currentPacket.data = newdata
//	s'.currentPacket.data = s.currentPacket.data
//}

pred Progress[s, s': State] {
	s'.End[] or
	(s.currentState = Call0FromAbove or s.currentState = Call1FromAbove implies
		#s.sendBuffer > #s'.sendBuffer and
		(s'.currentState = Call0FromBelow or s'.currentState = Call1FromBelow)
	else s.currentState = Call0FromBelow or s.currentState = Call1FromBelow implies
		#s'.recvBuffer >= #s.recvBuffer and
		(s'.currentState = Wait0ACKNAK or s'.currentState = Wait1ACKNAK)
	else s.currentState = Wait0ACKNAK or s.currentState = Wait1ACKNAK implies
		(s'.currentState = Call0FromBelow or s'.currentState = Call1FromBelow) or
		(s'.currentState = Call0FromAbove or s'.currentState = Call1FromAbove))
}

run Progress for exactly 5 State, 3 Data, 5 Packet, 3 Checksum

pred Trace {
	SO/first[].Init[]
	all s: State - SO/last[] | let s' = SO/next[s] |
		Progress[s, s'] and Step[s, s']
}

run Trace for 40 State,  exactly 3 Data,  6 Packet, exactly 3 Checksum//, exactly 2 SequenceNumber//, exactly 3 StateMarker

assert AlwaysTransmitted {
	Trace[]
}

//check AlwaysTransmitted for 4 State, exactly 3 Data, 5 Packet, exactly 3 Checksum//, exactly 2 SequenceNumber, exactly 3 StateMarker
