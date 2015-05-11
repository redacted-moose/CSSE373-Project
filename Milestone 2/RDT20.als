open util/ordering[State] as SO

sig Data {}
sig Checksum {}

one sig Check {
	sums: Data -> Checksum
}

fact {all d: Data | some c: Checksum | d = Check.sums.c and d.(Check.sums) = c}

abstract sig Packet {
	data: Data,
	checksum: Checksum
}

fact {all p: Packet | p.data = Check.sums.(p.checksum) and (p.data).(Check.sums) = p.checksum}

one sig NAK, ACK in Packet {}

sig State {
	sendBuffer: set Packet,
	recvBuffer: set Packet,

	lastSent: Packet
}


pred State.Init[] {
	this.sendBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
	#this.recvBuffer = 0
}

// run InitSend for 1 SendState, 1 RecvState, exactly 10 Data

pred State.End[] {
	#this.sendBuffer = 0
	this.recvBuffer = {p: Packet - NAK - ACK | p.checksum = (p.data).(Check.sums)}
}

// run Init for 1 SendState, 1 RecvState, exactly 10 Data

pred Step[s, s': State, p: Packet] {
	Send[s, s', p]
	GarbleData[p]
	Recv[s, s', p]
}

pred GarbleData[p: Packet] {
	some d: Data | p.data = d
}

pred Send[s, s': State, p: Packet] {
	s'.sendBuffer = s.sendBuffer - p and s.lastSent = p
}

pred SendNAKorACK[s, s': State, p: Packet] {
	p = NAK implies RecvAgain[s, s', s.lastSent]
	else p = ACK
}

pred Recv[s, s': State, p: Packet] {
	p.checksum = (p.data).(Check.sums) implies s'.recvBuffer = s.recvBuffer + p and SendNAKorACK[s, s', ACK]
	else p.checksum != (p.data).(Check.sums) implies SendNAKorACK[s, s', NAK]	
}

pred RecvAgain[s, s': State, p: Packet] {
	p.checksum = (p.data).(Check.sums) implies s'.recvBuffer = s.recvBuffer + p
}

run Step for exactly 2 State, exactly 4 Packet, exactly 4 Data, exactly 4 Checksum

// run SendStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

// run RecvStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

pred Progress[s, s': State] {
	(#s.sendBuffer > #s'.sendBuffer and #s.recvBuffer < #s'.recvBuffer) or
	s'.End[]
}

pred Trace {
	SO/first[].Init[]
	all s: State - SO/last[] | let s' = SO/next[s] |
		some p: s.sendBuffer | Progress[s, s'] and Step[s, s', p]
}

run Trace for 4 State,  exactly 3 Data, exactly 3 Packet, exactly 3 Checksum

assert AlwaysTransmitted {
	Trace[]
}

check AlwaysTransmitted for 4 State, exactly 3 Data, exactly 3 Packet, exactly 3 Checksum
