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
function CountSurvivorsFromRec(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n && left >= 0
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFromRec(n, a, start + 1, newLeft)
}

lemma CountSurvivorsFromAxiom(n: int, a: seq<int>)
    requires ValidInput(n, a)
    ensures CountSurvivors(n, a) == CountSurvivorsFromRec(n, a, 0, n)
{
    // axiom match
}

method ComputeSurvivors(n: int, a: seq<int>, start: int, left: int) returns (result: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n && left >= 0
    ensures result == CountSurvivorsFromRec(n, a, start, left)
{
    if start >= n {
        result := 0;
    } else {
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        var next := ComputeSurvivors(n, a, start + 1, newLeft);
        result := survives + next;
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
  result := ComputeSurvivors(n, a, 0, n);
}
// </vc-code>

