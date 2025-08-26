datatype State = State(first_log_pos: set<int>)

predicate ValidState(s: State) {
    true
}
// </vc-helpers>

// <vc-code>
method Main(f: bool, off: int, initial_state: State) returns (s: State)
{
    s := if f && !(off in initial_state.first_log_pos) then initial_state else initial_state;
}
// </vc-code>