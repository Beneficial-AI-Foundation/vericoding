//ATOM
// problem 5:
// name:   Gabriele Berardi
// s-number: s4878728
// table:   XXXX

ghost function f(n: int): int {
 if n < 0 then 0 else 3*f(n-5) + n
}

//IMPL problem5
method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    /* code modified by LLM (iteration 1): Fixed algorithm to properly compute f(n) iteratively by collecting terms and applying multipliers correctly */
    var i := n;
    x := 0;
    var multiplier := 1;
    
    while i >= 0
        invariant x + multiplier * f(i) == f(n)
        invariant multiplier >= 1
        decreases i
    {
        x := x + multiplier * i;
        if i < 5 {
            /* code modified by LLM (iteration 1): When i < 5, f(i-5) = f(negative) = 0, so we can terminate */
            break;
        }
        multiplier := multiplier * 3;
        i := i - 5;
    }
}