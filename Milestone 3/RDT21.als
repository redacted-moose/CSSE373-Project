open util/ordering[State] as SO

sig Data {}
sig Checksum {}

one sig Check {
	sums: Data -> Checksum
}

fact {all d: Data | one c: Checksum | d = Check.sums.c and d.(Check.sums) = c}

abstract sig SequenceNumber {}

one sig Number0, Number1 extends SequenceNumber {}

sig Packet {
	data: Data,
	checksum: Checksum,
	//sequenceNumber: SequenceNumber
}

//fact {	NAK.data = NAKData and NAK.checksum = NAKData.(Check.sums) and
//		ACK.data = ACKData and ACK.checksum = ACKData.(Check.sums)
//}

// Guarantees Packets will be uncorrupted, for testing
//fact {all p: Packet | p.data = Check.sums.(p.checksum) and (p.data).(Check.sums) = p.checksum}

one sig NAK, ACK extends Packet {}

abstract sig StateMarker {}

one sig CallFromAbove, WaitACKNAK, CallFromBelow extends StateMarker {}

sig State {
	sendBuffer: set Packet,
	recvBuffer: set Packet,

	lastSent: Packet, // Packet last sent by sender
	currentPacket: Packet, // Packet currently being sent

	currentState: StateMarker // Current state
}


pred State.Init[] {
	this.currentState = CallFromAbove
	this.sendBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
	#this.recvBuffer = 0
	//this.lastSent = NAK
}

run Init for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred State.End[] {
	#this.sendBuffer = 0
	this.recvBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
}

run End for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred Step[s, s': State] {
	s.currentState = CallFromAbove implies Send[s, s'] 
	else s.currentState = CallFromBelow implies Recv[s, s']
	else s.currentState = WaitACKNAK implies ResendIfNecessary[s, s']
}

run Step for exactly 5 Packet, exactly 3 Data, exactly 3 Checksum, exactly 2 State
run Step for exactly 2 State, exactly 6 Packet, exactly 4 Data, exactly 4 Checksum

fun GarbleData[p: Packet]: Packet {
	{p': Packet | some d: Data - p.data | p'.data = d and p'.checksum = p.checksum}
}

run GarbleData for exactly 1 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State

pred Send[s, s': State] {
	one p: s.sendBuffer | 
		s'.sendBuffer = s.sendBuffer - p and
		s'.lastSent = p and
		s'.currentPacket = p and
		s'.recvBuffer = s.recvBuffer and
		s'.currentState = CallFromBelow
}

run Send for exactly 2 State, exactly 3 Packet, exactly 1 Data, exactly 3 Checksum

pred Recv[s, s': State] {
	s'.currentState = WaitACKNAK and
	s'.sendBuffer = s.sendBuffer and
	s'.lastSent = s.lastSent and
	(isUncorrupt[s.currentPacket] implies
		s'.recvBuffer = s.recvBuffer + s.currentPacket and
		s'.currentPacket = ACK
	else isCorrupt[s.currentPacket] implies
		s'.recvBuffer = s.recvBuffer and
		s'.currentPacket = NAK)
}

run Recv for exactly 2 State, exactly 3 Packet, exactly 3 Data, exactly 3 Checksum

pred ResendIfNecessary[s, s': State] {
	s'.lastSent = s.lastSent and
	s'.sendBuffer = s.sendBuffer and
	s'.recvBuffer = s.recvBuffer and
	(isNAK[s.currentPacket] implies
		s'.currentPacket = s.lastSent and
		s'.currentState = CallFromBelow
	else isACK[s.currentPacket] implies
		s'.currentState = CallFromAbove and
		s'.currentPacket = s.currentPacket)
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

pred Progress[s, s': State] {
	s'.End[] or
	(s.currentState = CallFromAbove implies
		#s.sendBuffer > #s'.sendBuffer and
		s'.currentState = CallFromBelow
	else s.currentState = CallFromBelow implies
		#s'.recvBuffer >= #s.recvBuffer and
		s'.currentState = WaitACKNAK
	else s.currentState = WaitACKNAK implies
		s'.currentState = CallFromBelow or
		s'.currentState = CallFromAbove)
}

run Progress for exactly 5 State, 3 Data, 5 Packet, 3 Checksum

pred Trace {
	SO/first[].Init[]
	all s: State - SO/last[] | let s' = SO/next[s] |
		Progress[s, s'] and Step[s, s']
}

run Trace for 10 State,  exactly 3 Data, exactly 5 Packet, exactly 3 Checksum, exactly 2 SequenceNumber, exactly 3 StateMarker

assert AlwaysTransmitted {
	Trace[]
}

check AlwaysTransmitted for 4 State, exactly 3 Data, exactly 5 Packet, exactly 3 Checksum, exactly 2 SequenceNumber, exactly 3 StateMarker
