open util/ordering[State] as SO

sig Data {}

sig Packet {
	data: Data
}

sig State {
	sendBuffer: set Packet,
	recvBuffer: set Packet
}

pred State.Init[] {
	this.sendBuffer = Packet
	#this.recvBuffer = 0
}

// run InitSend for 1 SendState, 1 RecvState, exactly 10 Data

pred State.End[] {
	#this.sendBuffer = 0
	this.recvBuffer = Packet
}

// run Init for 1 SendState, 1 RecvState, exactly 10 Data

pred Step[s, s': State, p: Packet] {
	s'.sendBuffer = s.sendBuffer - p
	s'.recvBuffer = s.recvBuffer + p
}

// run SendStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

// run RecvStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

pred Progress[s, s': State] {
	(#s.sendBuffer > #s'.sendBuffer and #s.recvBuffer < #s'.recvBuffer) or
	s'.End[]
}

pred Trace {
	SO/first[].Init[]
	all s: State - SO/last[] | let s' = SO/next[s] |
		some p: Packet | Progress[s, s'] and Step[s, s', p]
}

run Trace for 3 State,  2 Data, 2 Packet

assert AlwaysTransmitted {
	Trace[]
}

check AlwaysTransmitted for 3 State, 2 Data, 2 Packet
