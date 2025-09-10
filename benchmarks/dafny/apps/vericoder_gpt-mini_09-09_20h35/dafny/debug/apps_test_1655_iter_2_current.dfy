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
lemma CountSurvivorsFromBounds(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    ensures 0 <= CountSurvivorsFrom(n, a, start, left) <= n - start
    decreases n - start
{
    if start >= n {
        assert CountSurvivorsFrom(n, a, start, left) == 0;
        // hence 0 <= 0 <= n - start (which is 0)
    } else {
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        // show recursive preconditions
        assert 0 <= start + 1 <= n;
        assert newLeft <= n;
        CountSurvivorsFromBounds(n, a, start + 1, newLeft);
        // unfold the function definition
        assert CountSurvivorsFrom(n, a, start, left) == survives + CountSurvivorsFrom(n, a, start + 1, newLeft);
        // survives is 0 or 1
        assert 0 <= survives <= 1;
        // use recursive bounds
        assert 0 <= CountSurvivorsFrom(n, a, start + 1, newLeft);
        assert CountSurvivorsFrom(n, a, start + 1, newLeft) <= n - (start + 1);
        // combine
        assert CountSurvivorsFrom(n, a, start, left) <= survives + (n - (start + 1));
        assert survives + (n - (start + 1)) <= 1 + (n - (start + 1));
        assert 1 + (n - (start + 1)) == n - start;
        assert 0 <= CountSurvivorsFrom(n, a, start, left);
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
  CountSurvivorsFromBounds(n, a, 0, n);
  result := CountSurvivors(n, a);
}
// </vc-code>

