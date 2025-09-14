predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < n ==> a[i] >= 0
}

function CountSurvivors(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    CountSurvivorsFrom(n, a, 0, n)
}

function CountSurvivorsFrom(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result <= n
    ensures result == CountSurvivors(n, a)
// </vc-spec>
// <vc-code>
{
    var left := n;
    var survivors := 0;
    var start := 0;
    while start < n
        invariant 0 <= start <= n
        invariant ValidInput(n, a)
        invariant left <= n
        invariant 0 <= survivors <= start
        invariant survivors + CountSurvivorsFrom(n, a, start, left) == CountSurvivors(n, a)
    {
        var i := n - 1 - start;
        if i < left {
            survivors := survivors + 1;
        }
        if i - a[i] < left {
            left := i - a[i];
        }
        start := start + 1;
    }
    result := survivors;
}
// </vc-code>

