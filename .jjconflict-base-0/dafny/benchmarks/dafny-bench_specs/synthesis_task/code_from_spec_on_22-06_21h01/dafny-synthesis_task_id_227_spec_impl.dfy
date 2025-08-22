//IMPL 
method MinOfThree(a: int, b: int, c: int) returns (min: int)
    ensures min <= a && min <= b && min <= c
    ensures (min == a) || (min == b) || (min == c)
{
    /* code modified by LLM (iteration 1): restructured conditional logic to ensure all cases are properly covered for verification */
    if a <= b && a <= c {
        min := a;
    } else if b <= a && b <= c {
        min := b;
    } else {
        min := c;
    }
}