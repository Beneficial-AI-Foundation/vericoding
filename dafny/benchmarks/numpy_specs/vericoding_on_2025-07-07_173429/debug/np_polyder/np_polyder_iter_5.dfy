//IMPL
method polyder (poly: array<real>, m: int) returns (ret: array<real>)
    requires m > 0
    ensures ret.Length == poly.Length - m 
{
    /* code modified by LLM (iteration 4): Added precondition check and fixed array bounds */
    if poly.Length <= m {
        ret := new real[0];
        return;
    }
    
    ret := new real[poly.Length - m];
    
    var i := 0;
    while i < ret.Length
        invariant 0 <= i <= ret.Length
        invariant ret.Length == poly.Length - m
        invariant poly.Length > m
        invariant forall k :: 0 <= k < i ==> 0 <= k + m < poly.Length
    {
        /* code modified by LLM (iteration 4): Added bounds check and fixed coefficient calculation */
        assert i + m < poly.Length; // This should hold from our invariants
        
        var coeff := poly[i + m];
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant coeff == poly[i + m] * real(factorial_partial(i + m, j))
        {
            coeff := coeff * real(i + m - j);
            j := j + 1;
        }
        ret[i] := coeff;
        i := i + 1;
    }
}

/* code modified by LLM (iteration 4): Added helper function for factorial computation reasoning */
function factorial_partial(n: int, steps: int): int
    requires n >= 0 && steps >= 0
{
    if steps == 0 then 1
    else if steps > n then 0
    else n * factorial_partial(n-1, steps-1)
}