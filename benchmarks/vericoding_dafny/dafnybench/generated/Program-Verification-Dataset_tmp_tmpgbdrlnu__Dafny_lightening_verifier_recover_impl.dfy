class State {
    var first_log_pos: set<int>
}

method Example(f: bool, off: int, s: State) 
{
    var result := if f && !(off in s.first_log_pos) then true else false;
}