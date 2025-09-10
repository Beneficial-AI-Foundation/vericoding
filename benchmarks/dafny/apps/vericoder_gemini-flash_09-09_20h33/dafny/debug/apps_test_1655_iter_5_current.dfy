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
        var newLeft_val := if i - a[i] < left then i - a[i] else left;
        
        // Ensure newLeft_val satisfies the precondition for the recursive call.
        // i - a[i] could be very small (e.g. i=0, a[i]=10000 -> -10000)
        // If left <= -n and i - a[i] < left, then i - a[i] would also be <= -n.
        // If left <= n, and left is positive, then i - a[i] could be negative.
        // If i - a[i] is between -n and n, then it's fine.
        // What if i - a[i] is greater than n? That is not possible as i is at most n-1.
        // So newLeft_val is either <= n or <= -n is guaranteed.
        
        CountSurvivorsFromIsCalcSurvivors(n, a, start + 1, newLeft_val);
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
    var currentLeft := n;

    var s_iter := 0;

    // Establish initial state for totalSurvivors:
    CountSurvivorsFromIsCalcSurvivors(n, a, 0, n); // This is needed to relate the two function definitions.

    while s_iter < n
        invariant 0 <= s_iter <= n
        invariant currentLeft <= n || currentLeft <= -n // It can go below -n if a[i] is large.
        invariant currentSurvivors == (CalcSurvivors(n, a, 0, n) - CalcSurvivors(n, a, s_iter, currentLeft as int))
        decreases n - s_iter
    {
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
        CountSurvivorsFromIsCalcSurvivors(n, a, s_iter + 1, newLeft_val);

        currentSurvivors := currentSurvivors + survives_val;
        currentLeft := newLeft_val;
        s_iter := s_iter + 1;
    }
    CountSurvivorsFromIsCalcSurvivors(n, a, s_iter, currentLeft as int); // For the final iteration where s_iter == n
    result := currentSurvivors;
}
// </vc-code>

