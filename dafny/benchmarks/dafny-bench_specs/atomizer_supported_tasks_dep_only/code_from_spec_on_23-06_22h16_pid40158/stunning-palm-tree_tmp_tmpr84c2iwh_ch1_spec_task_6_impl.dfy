// Ex 1.3
//ATOM Triple
method Triple(x: int) returns (r: int)
{
    r := 3 * x;
}

//ATOM Caller
method Caller()
{
    var result := Triple(18);
}

// Ex 1.6
//ATOM MinUnderSpec
method MinUnderSpec(x: int, y: int) returns (z: int)
    ensures z <= x && z <= y
{
    if x <= y {
        z := x;
    } else {
        z := y;
    }
}

//ATOM Min
method Min(x: int, y: int) returns (z: int)
    ensures z <= x && z <= y
    ensures z == x || z == y
{
    if x <= y {
        z := x;
    } else {
        z := y;
    }
}

// Ex 1.7
//IMPL MaxSum
method MaxSum (x: int, y: int) returns (s:int, m: int)
  ensures s == x + y
  ensures x <= m && y <= m
  ensures m == x || m == y
{
    /* code modified by LLM (iteration 1): Implementation to satisfy all postconditions */
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

//IMPL MaxSumCaller
method MaxSumCaller() {
    /* code modified by LLM (iteration 1): Fixed variable declaration syntax */
    var sum, max := MaxSum(5, 3);
}

// Ex 1.8
//ATOM ReconstructFromMaxSum
method ReconstructFromMaxSum(sum: int, max: int) returns (x: int, y: int)
    requires sum >= 2 * max
    ensures x + y == sum
    ensures (x <= max && y <= max)
    ensures (x == max || y == max)
{
    x := max;
    y := sum - max;
}

//ATOM TestMaxSum
method TestMaxSum()
{
    var s, m := MaxSum(5, 3);
    assert s == 8;
    assert m == 5;
}

// Ex 1.9
//ATOM Average
method Average(a: int, b: int) returns (avg: int)
    requires a >= 0 && b >= 0
    ensures 2 * avg == a + b
{
    avg := (a + b) / 2;
}

//ATOM Triple'
method Triple'(x: int) returns (r: int)
    ensures r == 3 * x
{
    r := x + x + x;
}