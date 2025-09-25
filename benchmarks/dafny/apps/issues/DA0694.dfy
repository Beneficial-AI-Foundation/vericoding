// <vc-preamble>
predicate ValidInput(n: int, m: int)
{
    n >= 0 && m >= 0 && n + m > 0
}

predicate canAssignHeights(n: int, m: int, maxHeight: int)
    requires n >= 0 && m >= 0 && maxHeight >= 0
{
    var multiplesOf2Only := maxHeight / 2 - maxHeight / 6;
    var multiplesOf3Only := maxHeight / 3 - maxHeight / 6;
    var multiplesOf6 := maxHeight / 6;

    var remainingN := if n <= multiplesOf2Only then 0 else n - multiplesOf2Only;
    var remainingM := if m <= multiplesOf3Only then 0 else m - multiplesOf3Only;

    multiplesOf6 >= remainingN + remainingM
}

predicate IsMinimalSolution(n: int, m: int, result: int)
    requires ValidInput(n, m)
{
    result > 0 &&
    canAssignHeights(n, m, result) &&
    (result > 1 ==> !canAssignHeights(n, m, result - 1))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
    requires ValidInput(n, m)
    ensures IsMinimalSolution(n, m, result)
// </vc-spec>
// <vc-code>
{
    var start := 0;
    var end := 6 * (n + m);

    while (!canAssignHeights(n, m, end))
        invariant end > 0
        decreases 100000 - end
    {
        end := end * 2;
        if end > 100000 {
            end := 100000;
            break;
        }
    }

    while (end - start > 1) 
        invariant 0 <= start < end
        invariant end > 0
        invariant !canAssignHeights(n, m, start) || start == 0
        invariant canAssignHeights(n, m, end)
        decreases end - start
    {
        var mid := (start + end) / 2;
        var two := mid / 2 - mid / 6;
        var three := mid / 3 - mid / 6;
        var six := mid / 6;

        var nn := n;
        var mm := m;

        nn := nn - two;
        mm := mm - three;
        if (nn < 0) { nn := 0; }
        if (mm < 0) { mm := 0; }

        if (six >= nn + mm) {
            end := mid;
        } else {
            start := mid;
        }
    }

    result := end;
}
// </vc-code>
