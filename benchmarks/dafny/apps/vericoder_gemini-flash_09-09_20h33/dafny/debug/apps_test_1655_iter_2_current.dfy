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
function CalcSurvivors(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n || left <= -n // Add left <= -n to cover cases where (i - a[i]) is very small.
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i >= 0 && i < n && i < left then 1 else 0;
        var newLeft := if i >= 0 && i < n && i - a[i] < left then i - a[i] else left;
        survives + CalcSurvivors(n, a, start + 1, newLeft)
}

lemma CountSurvivorsFromIsCalcSurvivors(n: int, a: seq<int>, start: int, left: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n || left <= -n // Matching the CalcSurvivors precondition
    ensures CountSurvivorsFrom(n, a, start, left) == CalcSurvivors(n, a, start, left)
    decreases n - start
{
    if (start < n) {
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;

        CountSurvivorsFromIsCalcSurvivors(n, a, start + 1, newLeft);
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
    var currentSurvivors := 0;
    var currentLeft := n; // This `left` variable maps to the `left` parameter

    var s_iter := 0; // This variable `s_iter` simulates the `start` parameter in the recursive function.
    while s_iter < n
        invariant 0 <= s_iter <= n
        invariant currentLeft <= n
        invariant currentLeft >= -n // A sufficiently loose lower bound for `currentLeft`
        invariant currentSurvivors == CountSurvivorsFrom(n, a, 0, n) - CountSurvivorsFrom(n, a, s_iter, currentLeft)
        invariant CountSurvivorsFromIsCalcSurvivors(n, a, s_iter, currentLeft) // Lemma linking
        decreases n - s_iter
    {
        var i_from_right := n - 1 - s_iter; // This is the array index being processed

        var survives_val := 0;
        if i_from_right < currentLeft {
            survives_val := 1;
        }

        var newLeft_val := currentLeft;
        if i_from_right - a[i_from_right] < newLeft_val {
            newLeft_val := i_from_right - a[i_from_right];
        }

        currentSurvivors := currentSurvivors + survives_val;
        currentLeft := newLeft_val;
        s_iter := s_iter + 1;
    }
    result := currentSurvivors;
}
// </vc-code>

