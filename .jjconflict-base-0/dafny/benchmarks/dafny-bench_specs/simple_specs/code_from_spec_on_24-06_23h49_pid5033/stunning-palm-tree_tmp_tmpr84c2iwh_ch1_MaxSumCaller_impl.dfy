//ATOM

// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
/* code modified by LLM (iteration 1): moved ensures clauses before method body and added implementation */
ensures s == x + y
ensures x <= m && y <= m
ensures m == x || m == y
{
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}


//IMPL MaxSumCaller
// look ma, no implementation!

method MaxSumCaller() {
/* code modified by LLM (iteration 1): added basic implementation body */
    var sum, max := MaxSum(5, 3);
}