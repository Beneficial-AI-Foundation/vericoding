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
    requires newLeft == (if i - a[i] < left then (if i - a[i] < 0 then 0 else i - a[i]) else left)
    ensures CountSurvivorsFrom(n, a, i, left) == 
            (if i < left then 1 else 0) + CountSurvivorsFrom(n, a, i + 1, newLeft)
{
    // This lemma helps establish the relationship between recursive calls
}

lemma CountSurvivorsFromMonotonic(n: int, a: seq<int>, start: int, left1: int, left2: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left1 <= left2 <= n
    ensures CountSurvivorsFrom(n, a, start, left1) >= CountSurvivorsFrom(n, a, start, left2)
    decreases n - start
{
    if start < n {
        var i := n - 1 - start;
        var newLeft1 := if i - a[i] < left1 then i - a[i] else left1;
        var newLeft2 := if i - a[i] < left2 then i - a[i] else left2;
        if i - a[i] < left1 {
            assert newLeft1 == (if i - a[i] < 0 then 0 else i - a[i]);
        } else {
            assert newLeft1 == left1;
        }
        if i - a[i] < left2 {
            assert newLeft2 == (if i - a[i] < 0 then 0 else i - a[i]);
        } else {
            assert newLeft2 == left2;
        }
        assert newLeft1 <= newLeft2;
        CountSurvivorsFromMonotonic(n, a, start + 1, newLeft1, newLeft2);
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
        invariant -1 <= i < n || i == -1
        invariant 0 <= left <= n
        invariant result >= 0
        invariant result + CountSurvivorsFrom(n, a, i + 1, left) == CountSurvivors(n, a)
    {
        var survives := 0;
        var newLeft := left;
        if i < left {
            survives := 1;
            result := result + survives;
            var candidate := i - a[i];
            if candidate < 0 {
                newLeft := 0;
            } else {
                newLeft := candidate;
            }
        } else {
            newLeft := left;
        }
        CountSurvivorsFromRelation(n, a, i, left, newLeft);
        left := newLeft;
        i := i - 1;
    }
}
// </vc-code>

