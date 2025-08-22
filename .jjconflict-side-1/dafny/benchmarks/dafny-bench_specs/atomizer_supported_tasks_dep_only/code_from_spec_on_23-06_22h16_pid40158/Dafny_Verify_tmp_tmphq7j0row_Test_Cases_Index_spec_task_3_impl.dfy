//ATOM Index
predicate Index(s: seq<int>, i: int) {
    0 <= i < |s|
}

//ATOM Min
function Min(x: int, y: int): int {
    if x <= y then x else y
}

//IMPL Max
method Max(x: int, y: int) returns (m: int)
    ensures m == x || m == y
    ensures m >= x && m >= y
{
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

//ATOM Sum
function Sum(s: seq<int>): int {
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

//ATOM SumCaller
method SumCaller(s: seq<int>) returns (total: int)
    ensures total == Sum(s)
{
    total := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant total == Sum(s[..i])
    {
        total := total + s[i];
        i := i + 1;
    }
}

//ATOM ReconstructFromMaxSum
method ReconstructFromMaxSum(maxVal: int, sumVal: int) returns (x: int, y: int)
    requires maxVal >= sumVal - maxVal
    ensures x + y == sumVal
    ensures (x >= y ? x : y) == maxVal
{
    if maxVal * 2 >= sumVal {
        x := maxVal;
        y := sumVal - maxVal;
    } else {
        y := maxVal;
        x := sumVal - maxVal;
    }
}

//ATOM TestMaxSum
method TestMaxSum() {
    /* code modified by LLM (iteration 1): Fixed method call syntax - methods require explicit return parameter assignment */
    var m := Max(5, 3);
    assert m == 5;
    
    /* code modified by LLM (iteration 1): Fixed method call syntax - methods require explicit return parameter assignment */
    var s := [1, 2, 3, 4];
    var total := SumCaller(s);
    assert total == 10;
}