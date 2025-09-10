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
    requires left <= n || left <= -n  // Add left <= -n to cover cases where (i - a[i]) is very small.
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
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
    // The loop computes CountSurvivorsFrom(n,a,0,n) - CountSurvivorsFrom(n,a,s_iter,currentLeft)
    // where CountSurvivorsFrom(n,a,0,n) initially is 0 and s_iter starts at 0.
    // After each iteration, currentSurvivors has accumulated to be CountSurvivorsFrom(n,a,0,n) - CountSurvivorsFrom(n,a,s_iter,currentLeft)
    // (where s_iter and currentLeft are the values *after* the iteration)
    // So the invariant we are trying to establish is `currentSurvivors + CountSurvivorsFrom(n,a,s_iter,currentLeft) == CountSurvivorsFrom(n,a,0,n)`
    // where CountSurvivorsFrom(n,a,0,n) is the total number of survivors.
    // Let's call totalSurvivors = CountSurvivorsFrom(n,a,0,n)
    // So, `currentSurvivors == totalSurvivors - CountSurvivorsFrom(n,a,s_iter,currentLeft)`

    // Establish initial state for totalSurvivors:
    // When s_iter is 0, currentLeft is n.
    // CountSurvivorsFromIsCalcSurvivors(n, a, 0, n); // This is needed to relate the two function definitions.

    while s_iter < n
        invariant 0 <= s_iter <= n
        invariant currentLeft <= n || currentLeft <= -n // It can go below -n if a[i] is large.
        invariant currentSurvivors == (CalcSurvivors(n, a, 0, n) - CalcSurvivors(n, a, s_iter, currentLeft as int))
        decreases n - s_iter
    {
        // Prove the lemma here explicitly
        // This lemma relates CountSurvivorsFrom to CalcSurvivors, which is what we are using in the invariant.
        CountSurvivorsFromIsCalcSurvivors(n, a, s_iter, currentLeft as int); // Assert currentLeft can be negative
        CountSurvivorsFromIsCalcSurvivors(n, a, 0, n); // For the total survivors value.

        var i_from_right := n - 1 - s_iter; // This is the array index being processed

        var survives_val := 0;
        if i_from_right < currentLeft {
            survives_val := 1;
        }

        var newLeft_val := currentLeft;
        if i_from_right - a[i_from_right] < newLeft_val {
            newLeft_val := i_from_right - a[i_from_right];
        }

        // We need to prove the invariant holds for the next iteration.
        // That is, prior_currentSurvivors + survives_val == totalSurvivors - CountSurvivorsFrom(n,a,s_iter+1, newLeft_val)
        // prior_currentSurvivors == totalSurvivors - CountSurvivorsFrom(n,a,s_iter, currentLeft)
        // So, totalSurvivors - CountSurvivorsFrom(n,a,s_iter, currentLeft) + survives_val == totalSurvivors - CountSurvivorsFrom(n,a,s_iter+1, newLeft_val)
        // This simplifies to survives_val == CountSurvivorsFrom(n,a,s_iter, currentLeft) - CountSurvivorsFrom(n,a,s_iter+1, newLeft_val)
        // Which is exactly how CountSurvivorsFrom is defined for one step.

        currentSurvivors := currentSurvivors + survives_val;
        currentLeft := newLeft_val;
        s_iter := s_iter + 1;
    }
    CountSurvivorsFromIsCalcSurvivors(n, a, s_iter, currentLeft as int); // For the final iteration where s_iter == n
    result := currentSurvivors;
    // When s_iter == n, CountSurvivorsFrom(n, a, n, currentLeft) == 0 (by definition of CountSurvivorsFrom)
    // So currentSurvivors == CalcSurvivors(n, a, 0, n) - 0
    // currentSurvivors == CalcSurvivors(n, a, 0, n)
    // And CalcSurvivors(n,a,0,n) == CountSurvivors(n,a)
}
// </vc-code>

