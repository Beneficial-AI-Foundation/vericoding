//ATOM 
// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

//IMPL 

method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    /* code modified by LLM (iteration 2): Completely rewrote algorithm to properly compute f(n) iteratively */
    x := 0;
    var i := n;
    var multiplier := 1;
    
    while i >= 0
        invariant x + multiplier * f(i) == f(n)
        invariant multiplier >= 1
        decreases i
    {
        if i < 5 {
            /* code modified by LLM (iteration 2): Handle base case where f(i-5) would be f(negative) = 0 */
            x := x + multiplier * i;
            break;
        }
        /* code modified by LLM (iteration 2): Apply the recursive relation f(i) = 3*f(i-5) + i */
        x := x + multiplier * i;
        multiplier := multiplier * 3;
        i := i - 5;
    }
}