//IMPL
method polyder (poly: array<real>, m: int) returns (ret: array<real>)
    requires m > 0
    ensures ret.Length == poly.Length - m 
{
    /* code modified by LLM (iteration 4): Added proper precondition handling without assert false */
    if poly.Length < m {
        ret := new real[0];
        return;
    }
    
    /* code modified by LLM (iteration 4): Create result array with correct size */
    ret := new real[poly.Length - m];
    
    /* code modified by LLM (iteration 4): Simplified derivative calculation */
    var i := 0;
    while i < ret.Length
        invariant 0 <= i <= ret.Length
        invariant ret.Length == poly.Length - m
        invariant poly.Length >= m
    {
        /* code modified by LLM (iteration 4): Calculate m-th derivative coefficient */
        var coeff := poly[i + m];
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant i + m - j >= 1 || j == 0
        {
            coeff := coeff * real(i + m - j);
            j := j + 1;
        }
        ret[i] := coeff;
        i := i + 1;
    }
}