open util/ordering[State] as SO

sig Data {}
//one sig NAKData, ACKData extends Data {}
sig Checksum {}

one sig Check {
	sums: Data -> Checksum
}

fact {all d: Data | some c: Checksum | d = Check.sums.c and d.(Check.sums) = c}

sig Packet {
	data: Data,
	checksum: Checksum
}

//fact {	NAK.data = NAKData and NAK.checksum = NAKData.(Check.sums) and
//		ACK.data = ACKData and ACK.checksum = ACKData.(Check.sums)
//}

// Guarantees Packets will be uncorrupted, for testing
//fact {all p: Packet | p.data = Check.sums.(p.checksum) and (p.data).(Check.sums) = p.checksum}

one sig NAK, ACK extends Packet {}

sig State {
	sendBuffer: set Packet,
	recvBuffer: set Packet,

	lastSent: Packet
}


pred State.Init[] {
	this.sendBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
	#this.recvBuffer = 0
	this.lastSent = NAK
}

run Init for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred State.End[] {
	#this.sendBuffer = 0
	this.recvBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
}

run End for 1 State, exactly 5 Data, exactly 5 Checksum, exactly 7 Packet

pred Step[s, s': State, p: Packet] {
	Send[s, s', p]
//	GarbleData[p]
	
}

run Step for exactly 5 Packet, exactly 3 Data, exactly 3 Checksum, exactly 2 State
run Step for exactly 2 State, exactly 6 Packet, exactly 4 Data, exactly 4 Checksum

pred GarbleData[p: Packet] {
	some d: Data - p.data | p.data = d
}

run GarbleData for exactly 1 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State

pred Send[s, s': State, p: Packet] {
	s'.sendBuffer = s.sendBuffer - p and s'.lastSent = p
	//GarbleData[p]
	Recv[s, s', p]
}

run Send for exactly 2 State, exactly 3 Packet, exactly 1 Data, exactly 3 Checksum

pred SendNAKorACK[s, s': State, p: Packet] {
	p = NAK implies RecvAgain[s, s', s'.lastSent]
	//else p = ACK
}

pred Recv[s, s': State, p: Packet] {
	isUncorrupt[p] implies s'.recvBuffer = s.recvBuffer + p and SendNAKorACK[s, s', ACK]
	else !isUncorrupt[p] implies s'.recvBuffer = s.recvBuffer and SendNAKorACK[s, s', NAK] 	
}

run Recv for exactly 2 State, exactly 3 Packet, exactly 3 Data, exactly 3 Checksum

pred RecvAgain[s, s': State, p: Packet] {
	isUncorrupt[p] implies s'.recvBuffer = s.recvBuffer + p
}

pred isUncorrupt[p: Packet] {
	p.checksum = (p.data).(Check.sums)
}

assert AlwaysUncorrupt {
	all p: Packet | isUncorrupt[p]
}

run isUncorrupt for exactly 2 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State

check AlwaysUncorrupt for exactly 2 Packet, exactly 2 Data, exactly 2 Checksum, exactly 1 State



// run SendStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

// run RecvStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

pred Progress[s, s': State] {
	(#s.sendBuffer > #s'.sendBuffer and #s.recvBuffer < #s'.recvBuffer) or
	s'.End[]
}

run Progress for exactly 5 State, 3 Data, 5 Packet, 3 Checksum

pred Trace {
	SO/first[].Init[]
//	all s: State - SO/last[] | let s' = SO/next[s] |
	//	some p: s.sendBuffer | Progress[s, s'] and Step[s, s', p]
}

run Trace for 10 State,  exactly 3 Data, exactly 5 Packet, exactly 3 Checksum

assert AlwaysTransmitted {
	Trace[]
}

check AlwaysTransmitted for 4 State, exactly 3 Data, exactly 5 Packet, exactly 3 Checksum
