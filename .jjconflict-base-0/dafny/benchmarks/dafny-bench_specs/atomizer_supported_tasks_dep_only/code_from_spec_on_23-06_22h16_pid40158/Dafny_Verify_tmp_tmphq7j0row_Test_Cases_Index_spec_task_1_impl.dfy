//IMPL 
method Index(n: int) returns (i: int) 
requires 1 <= n
ensures 0 <= i < n
{
    /* code modified by LLM (iteration 3): set i to 0 with explicit verification help */
    i := 0;
    assert 0 <= i;
    assert i < n;
}

//ATOM Min
function Min(a: int, b: int): int
{
    if a <= b then a else b
}

//ATOM Max
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

//ATOM MaxSum
function MaxSum(arr: seq<int>): int
requires |arr| > 0
{
    if |arr| == 1 then arr[0]
    else Max(arr[0], arr[0] + MaxSum(arr[1..]))
}

//ATOM MaxSumCaller
method MaxSumCaller(arr: seq<int>) returns (result: int)
requires |arr| > 0
{
    result := MaxSum(arr);
}

//ATOM ReconstructFromMaxSum
method ReconstructFromMaxSum(arr: seq<int>) returns (maxSum: int, startIndex: int, endIndex: int)
requires |arr| > 0
ensures 0 <= startIndex <= endIndex < |arr|
{
    maxSum := MaxSum(arr);
    startIndex := 0;
    endIndex := 0;
}

//ATOM TestMaxSum
method TestMaxSum()
{
    var arr := [1, -2, 3, 4, -1];
    var result := MaxSumCaller(arr);
    assert result == MaxSum(arr);
}