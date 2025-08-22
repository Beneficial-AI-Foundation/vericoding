//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 4): Fixed length calculation with proper Floor operation */
    var diff := stop - start;
    var quotient := diff / step;
    var length := quotient.Floor;
    
    /* code modified by LLM (iteration 4): Added comprehensive assertions to prove length properties */
    if step > 0.0 {
        assert start < stop;
        assert diff > 0.0;
        assert quotient > 0.0;
    } else {
        assert start > stop;
        assert diff < 0.0;
        assert step < 0.0;
        assert quotient > 0.0;
    }
    
    /* code modified by LLM (iteration 4): Ensure length is positive */
    assert quotient > 0.0;
    assert length >= 1;
    
    ret := new real[length];
    
    /* code modified by LLM (iteration 4): Initialize first element to establish ret[0] == start */
    ret[0] := start;
    
    var i := 1;
    while i < length
        invariant 1 <= i <= length
        invariant ret[0] == start
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * (j as real)
        /* code modified by LLM (iteration 4): Maintain consecutive difference invariant */
        invariant forall j :: 1 <= j < i ==> ret[j] - ret[j-1] == step
    {
        /* code modified by LLM (iteration 4): Set array elements with proper formula */
        ret[i] := start + step * (i as real);
        
        /* code modified by LLM (iteration 4): Assert the consecutive difference property */
        assert ret[i-1] == start + step * ((i-1) as real);
        assert ret[i] - ret[i-1] == (start + step * (i as real)) - (start + step * ((i-1) as real));
        assert ret[i] - ret[i-1] == step * ((i as real) - ((i-1) as real));
        assert ret[i] - ret[i-1] == step * 1.0;
        assert ret[i] - ret[i-1] == step;
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Final assertions to establish all postconditions */
    assert ret[0] == start;
    assert ret.Length == length;
    assert length == ((stop - start)/step).Floor;
    
    /* code modified by LLM (iteration 4): Prove consecutive differences for all valid indices */
    assert forall j :: 1 <= j < ret.Length ==> ret[j] == start + step * (j as real);
    assert forall j :: 1 <= j < ret.Length ==> ret[j-1] == start + step * ((j-1) as real);
}