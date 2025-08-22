//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 1): Added length positivity assertion and improved loop invariants */
    var length := ((stop - start) / step).Floor;
    
    // Ensure length is positive based on preconditions
    assert length > 0;
    
    ret := new real[length];
    
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * j.real
        /* code modified by LLM (iteration 1): Added invariant for consecutive differences */
        invariant forall j :: 1 <= j < i ==> ret[j] - ret[j-1] == step
    {
        ret[i] := start + step * i.real;
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertions to help prove postconditions */
    assert ret[0] == start + step * 0.real == start;
    assert forall j :: 1 <= j < ret.Length ==> ret[j] - ret[j-1] == (start + step * j.real) - (start + step * (j-1).real) == step;
}