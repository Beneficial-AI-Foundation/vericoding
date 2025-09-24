// <vc-preamble>
predicate ValidInput(n: int, a: seq<int>)
{
    2 <= n <= 100000 && |a| == n && forall i :: 0 <= i < n ==> 1 <= a[i] <= 100000
}

predicate IsSorted(a: seq<int>)
{
    forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i+1]
}

function CircularDiff(a: seq<int>, i: int): int
    requires |a| > 0
    requires 0 <= i < |a|
{
    if i == |a| - 1 then a[0] - a[i] else a[i+1] - a[i]
}

predicate ValidResult(n: int, a: seq<int>, result: int)
    requires ValidInput(n, a)
{
    result == -1 || (0 <= result < n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidResult(n, a, result)
// </vc-spec>
// <vc-code>
{
    var d := new int[n];

    // Calculate differences
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall j :: 0 <= j < i-1 ==> d[j] == a[j+1] - a[j]
    {
        d[i-1] := a[i] - a[i-1];
        i := i + 1;
    }
    d[n-1] := a[0] - a[n-1];

    // Count negative differences
    var cnt := 0;
    var pos := -1;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant cnt >= 0
        invariant cnt <= i
        invariant pos == -1 || (0 <= pos < i)
        invariant forall j :: 0 <= j < i && d[j] < 0 ==> j <= pos
        invariant cnt > 0 ==> (pos != -1 && 0 <= pos < i && d[pos] < 0)
        invariant cnt == 0 ==> pos == -1
    {
        if d[i] < 0 {
            cnt := cnt + 1;
            pos := i;
        }
        i := i + 1;
    }

    if cnt == 0 {
        result := 0;
    } else if cnt > 1 {
        result := -1;
    } else {
        assert cnt == 1;
        assert pos != -1 && 0 <= pos < n;
        result := n - pos - 1;
    }
}
// </vc-code>
