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
lemma CountSurvivorsFromDecreases(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    ensures CountSurvivorsFrom(n, a, start, left) >= 0
    decreases n - start
{
    if start < n {
        var i := n - 1 - start;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        CountSurvivorsFromDecreases(n, a, start + 1, newLeft);
    }
}
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
    result := 0;
    var left := n;
    var i := n - 1;
    while i >= 0
        invariant -1 <= i <= n - 1
        invariant 0 <= left <= n
        invariant result >= 0
        invariant result + CountSurvivorsFrom(n, a, i + 1, left) == CountSurvivors(n, a)
    {
        if i < left {
            result := result + 1;
            left := i - a[i];
        } else {
            left := left;
        }
        i := i - 1;
    }
}
// </vc-code>

