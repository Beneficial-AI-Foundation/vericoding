//IMPL
/* code modified by LLM (iteration 4): Added helper function outside method */
function Floor(x: real): int
    requires x >= 0.0
{
    if x < 1.0 then 0
    else 1 + Floor(x - 1.0)
}

method arange(start: real, stop: real, step: real) returns (ret: array<real>)
    requires if step < 0.0 then start > stop else start < stop
    requires step != 0.0
    ensures ret.Length == ((stop - start)/step).Floor 
    ensures ret.Length > 0
    ensures ret[0] == start
    ensures forall i :: 1 <= i < ret.Length ==> ret[i] - ret[i-1] == step
{
    /* code modified by LLM (iteration 4): Simplified length calculation using proper floor logic */
    var diff := stop - start;
    var quotient := diff / step;
    
    // quotient is always positive due to preconditions
    assert quotient > 0.0;
    
    /* code modified by LLM (iteration 4): Use integer conversion for floor approximation */
    var length := (quotient as int);
    if (length as real) > quotient {
        length := length - 1;
    }
    
    /* code modified by LLM (iteration 4): Ensure we have at least one element */
    if length <= 0 {
        length := 1;
    }
    
    /* code modified by LLM (iteration 4): Assert that our length matches the specification */
    assert length == Floor(quotient);
    assert length > 0;
    
    ret := new real[length];
    
    /* code modified by LLM (iteration 4): Fill array with arithmetic progression */
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant forall j :: 0 <= j < i ==> ret[j] == start + step * (j as real)
        invariant forall j :: 1 <= j < i ==> ret[j] - ret[j-1] == step
    {
        ret[i] := start + step * (i as real);
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Final assertions to establish postconditions */
    assert ret[0] == start;
    assert forall j :: 1 <= j < ret.Length ==> ret[j] - ret[j-1] == step;
}