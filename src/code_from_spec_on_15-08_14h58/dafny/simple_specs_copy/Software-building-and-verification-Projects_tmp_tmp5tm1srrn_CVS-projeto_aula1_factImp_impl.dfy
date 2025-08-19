//IMPL 
/* code modified by LLM (iteration 1): removed invalid text and added loop invariants for verification */
method factImp(n: int) returns (r: int)
{
    if n <= 0 {
        r := 1;
    } else {
        r := 1;
        var i := 1;
        while i <= n
            invariant 1 <= i <= n + 1
            invariant r >= 1
        {
            r := r * i;
            i := i + 1;
        }
    }
}