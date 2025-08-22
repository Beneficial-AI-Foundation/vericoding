//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 4): Simplified quotient calculation with proper Floor handling */
    var quotient := (stop - start) / step;
    
    // Establish that quotient > 0 from preconditions
    if step > 0.0 {
        assert start < stop;
        assert stop - start > 0.0;
        assert quotient > 0.0;
    } else {
        assert step < 0.0;
        assert start > stop;
        assert stop - start < 0.0;
        assert quotient > 0.0;
    }
    
    /* code modified by LLM (iteration 4): Direct Floor calculation */
    var length := quotient.Floor;
    assert length > 0;
    
    ret := new real[length];
    
    /* code modified by LLM (iteration 4): Initialize first element */
    ret[0] := start;
    
    /* code modified by LLM (iteration 4): Simplified loop with clearer invariants */
    var i := 1;
    while i < length
        invariant 1 <= i <= length
        invariant ret.Length == length
        invariant ret[0] == start
        invariant forall j :: 1 <= j < i ==> ret[j] == start + step * (j as real)
        invariant forall k :: 1 <= k < i ==> ret[k] - ret[k-1] == step
    {
        /* code modified by LLM (iteration 4): Element assignment */
        ret[i] := start + step * (i as real);
        
        /* code modified by LLM (iteration 4): Prove consecutive difference property */
        assert ret[i-1] == start + step * ((i-1) as real);
        assert ret[i] == start + step * (i as real);
        assert ret[i] - ret[i-1] == start + step * (i as real) - (start + step * ((i-1) as real));
        assert ret[i] - ret[i-1] == step * (i as real) - step * ((i-1) as real);
        assert ret[i] - ret[i-1] == step * ((i as real) - ((i-1) as real));
        assert ret[i] - ret[i-1] == step * 1.0;
        assert ret[i] - ret[i-1] == step;
        
        i := i + 1;
    }
}