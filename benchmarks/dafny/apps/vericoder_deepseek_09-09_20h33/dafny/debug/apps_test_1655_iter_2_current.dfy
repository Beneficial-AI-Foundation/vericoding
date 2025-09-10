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

lemma CountSurvivorsFromRelation(n: int, a: seq<int>, i: int, left: int, newLeft: int)
    requires ValidInput(n, a)
    requires 0 <= i < n
    requires left <= n
    requires newLeft == (if i - a[i] < left then i - a[i] else left)
    ensures CountSurvivorsFrom(n, a, i, left) == 
            (if i < left then 1 else 0) + CountSurvivorsFrom(n, a, i + 1, newLeft)
{
    // This lemma helps establish the relationship between recursive calls
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
        var newLeft := left;
        if i < left {
            result := result + 1;
            newLeft := i - a[i];
            // Ensure newLeft is within bounds
            assert 0 <= newLeft <= n;
        }
        CountSurvivorsFromRelation(n, a, i, left, newLeft);
        left := newLeft;
        i := i - 1;
    }
}
// </vc-code>

