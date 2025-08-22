//IMPL
method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 2): Fixed Floor operation and added proper length calculation */
    var diff := stop - start;
    var quotient := diff / step;
    var length := quotient.Floor;
    
    /* code modified by LLM (iteration 2): Added assertion to prove length is positive */
    if step > 0.0 {
        assert start < stop;
        assert diff > 0.0;
        assert quotient > 0.0;
        assert length > 0;
    } else {
        assert start > stop;
        assert diff < 0.0;
        assert quotient > 0.0;
        assert length > 0;
    }
    
    ret := new real[length];
    
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * (j as real)
        /* code modified by LLM (iteration 2): Fixed invariant for consecutive differences */
        invariant forall j :: 1 <= j < i ==> ret[j] - ret[j-1] == step
    {
        /* code modified by LLM (iteration 2): Fixed integer to real conversion */
        ret[i] := start + step * (i as real);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): Added final assertions to establish postconditions */
    assert ret[0] == start + step * (0 as real) == start;
    assert forall j :: 1 <= j < ret.Length ==> 
        ret[j] - ret[j-1] == (start + step * (j as real)) - (start + step * ((j-1) as real)) == step * ((j as real) - ((j-1) as real)) == step * 1.0 == step;
}