// <vc-preamble>
predicate ValidInput(n: int, m: int, v: seq<int>, ropes: seq<(int, int)>)
{
    n > 0 &&
    m >= 0 &&
    |v| == n &&
    |ropes| == m &&
    (forall i :: 0 <= i < n ==> 0 <= v[i] <= 100000) &&
    (forall i :: 0 <= i < m ==> 1 <= ropes[i].0 <= n && 1 <= ropes[i].1 <= n) &&
    (forall i :: 0 <= i < m ==> ropes[i].0 != ropes[i].1)
}

function sumRopeCosts(v: seq<int>, ropes: seq<(int, int)>, i: int): int
requires 0 <= i <= |ropes|
requires forall j :: 0 <= j < |ropes| ==> 1 <= ropes[j].0 <= |v| && 1 <= ropes[j].1 <= |v|
{
    if i == 0 then 0
    else sumRopeCosts(v, ropes, i-1) + min(v[ropes[i-1].0-1], v[ropes[i-1].1-1])
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int
{
    if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, v: seq<int>, ropes: seq<(int, int)>) returns (result: int)
requires ValidInput(n, m, v, ropes)
ensures result == sumRopeCosts(v, ropes, m)
ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    for i := 0 to m
    invariant sum == sumRopeCosts(v, ropes, i)
    invariant sum >= 0
    {
        var x := ropes[i].0;
        var y := ropes[i].1;
        var minVal := if v[x-1] < v[y-1] then v[x-1] else v[y-1];
        sum := sum + minVal;
    }
    result := sum;
}
// </vc-code>
