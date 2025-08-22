//IMPL
method polyder (poly: array<real>, m: int) returns (ret: array<real>)
    requires m > 0
    ensures ret.Length == poly.Length - m 
{
    /* code modified by LLM (iteration 1): Added condition to handle case where poly.Length <= m properly */
    if poly.Length <= m {
        ret := new real[poly.Length - m];
    } else {
        ret := new real[poly.Length - m];
        var i := 0;
        while i < ret.Length
            invariant 0 <= i <= ret.Length
        {
            var coeff := poly[i + m];
            var j := 0;
            while j < m
                invariant 0 <= j <= m
            {
                coeff := coeff * (real(i + m - j));
                j := j + 1;
            }
            ret[i] := coeff;
            i := i + 1;
        }
    }
}