open util/ordering[SendState] as SSO
open util/ordering[RecvState] as RSO

sig Data {}
sig SendState {
	buffer: set Data
}
sig RecvState {
	buffer: set Data
}

pred SendState.InitSend[] {
	this.buffer = Data
}

run InitSend for 1 SendState, 1 RecvState, exactly 10 Data

pred SendState.End[] {
	#this.buffer = 0
}

pred RecvState.Init[] {
	#this.buffer = 0
}

run Init for 1 SendState, 1 RecvState, exactly 10 Data

pred RecvState.End[] {
	this.buffer = Data
}

pred SendStep[s, s': SendState, d: Data] {
	s'.buffer = s.buffer - d
}

run SendStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

pred RecvStep[s, s': RecvState, d: Data] {
	s'.buffer = s.buffer + d
}

run RecvStep for exactly 2 SendState, exactly 2 RecvState, exactly 2 Data

pred Progress[ss, ss': SendState, rs, rs': RecvState] {
	(#ss.buffer > #ss'.buffer and #rs.buffer < #rs'.buffer) or
	(ss'.End[] and rs'.End[])
}

pred Trace {
	SSO/first[].InitSend[]
	RSO/first[].Init[]
	all ss: SendState - SSO/last[], rs: RecvState - RSO/last[] | let ss' = SSO/next[ss], rs' = RSO/next[rs]|
		some d: Data | Progress[ss, ss', rs, rs'] and SendStep[ss, ss', d] and RecvStep[rs, rs', d]
}

run Trace for 2 SendState, 2 RecvState,  1 Data

assert AlwaysTransmitted {
	Trace[]
}

check AlwaysTransmitted for 3 SendState, 3 RecvState, 2 Data
