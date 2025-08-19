//ATOM
// Ex 1.7
method MaxSum (x: int, y: int) returns (s:int, m: int)
 ensures s == x + y
 ensures x <= m && y <= m
 ensures m == x || m == y
{
    /* code modified by LLM (iteration 1): Added body implementation for MaxSum method to fix compilation error */
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

//IMPL 

method MaxSumCaller() {
    /* code modified by LLM (iteration 1): Added complete implementation for MaxSumCaller method */
    var sum, max := MaxSum(3, 5);
    assert sum == 8;
    assert max == 5;
    
    var sum2, max2 := MaxSum(10, 7);
    assert sum2 == 17;
    assert max2 == 10;
}