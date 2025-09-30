predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 0 && k <= n
}

predicate ValidOutput(result: seq<int>, n: int, k: int)
{
    |result| == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

function MinGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0 else 1
}

function MaxGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0
    else if n - k < k * 2 then n - k
    else k * 2
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == MinGoodApartments(n, k)
    ensures result[1] == MaxGoodApartments(n, k)
// </vc-spec>
// <vc-code>
{
    var min := if k == 0 || k == n then 0 else 1;
    var max := if k == 0 || k == n then 0
               else if n - k < k * 2 then n - k
               else k * 2;
    
    result := [min, max];
}
// </vc-code>

