//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 3): Fixed Floor operation and added proper length calculation */
    var diff := stop - start;
    var quotient := diff / step;
    var length := quotient.Floor;
    
    /* code modified by LLM (iteration 3): Added proper assertions to prove length is positive */
    if step > 0.0 {
        assert start < stop;
        assert diff > 0.0;
        assert quotient > 0.0;
        assert length >= 1;
    } else {
        assert start > stop;
        assert diff < 0.0;
        assert step < 0.0;
        assert quotient > 0.0;
        assert length >= 1;
    }
    
    ret := new real[length];
    
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * (j as real)
        /* code modified by LLM (iteration 3): Strengthened invariant for consecutive differences */
        invariant forall j :: 1 <= j < i ==> ret[j] - ret[j-1] == step
    {
        /* code modified by LLM (iteration 3): Fixed assignment with proper real conversion */
        ret[i] := start + step * (i as real);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 3): Added assertions to establish postconditions */
    assert ret[0] == start + step * 0.0 == start;
    
    /* code modified by LLM (iteration 3): Prove the consecutive difference property */
    forall j | 1 <= j < ret.Length 
        ensures ret[j] - ret[j-1] == step
    {
        assert ret[j] == start + step * (j as real);
        assert ret[j-1] == start + step * ((j-1) as real);
        assert ret[j] - ret[j-1] == (start + step * (j as real)) - (start + step * ((j-1) as real));
        assert ret[j] - ret[j-1] == step * ((j as real) - ((j-1) as real));
        assert ret[j] - ret[j-1] == step * 1.0;
        assert ret[j] - ret[j-1] == step;
    }
}