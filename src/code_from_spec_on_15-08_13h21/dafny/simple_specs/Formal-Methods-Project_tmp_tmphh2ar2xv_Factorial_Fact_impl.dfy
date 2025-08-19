//IMPL 
method Fact(x: int) returns (y: int)
/* code modified by LLM (iteration 1): removed deprecated semicolon after requires clause */
requires x >= 0
{
    if x == 0 {
        y := 1;
    } else {
        var i := 1;
        y := 1;
        while i <= x
            invariant 1 <= i <= x + 1
            invariant y >= 1
        {
            y := y * i;
            i := i + 1;
        }
    }
}