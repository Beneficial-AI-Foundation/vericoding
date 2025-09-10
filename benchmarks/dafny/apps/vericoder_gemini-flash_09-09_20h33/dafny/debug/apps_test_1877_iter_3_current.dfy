predicate ValidInput(n: int, s: string)
{
    n >= 0 && |s| == n && forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
}

function CountKingdomTransitions(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountKingdomTransitions(s) >= 0
    ensures CountKingdomTransitions(s) <= |s|
{
    if |s| == 0 then 0
    else CountTransitionsHelper(s, 0, 0, 0, -1)
}

function CountTransitionsHelper(s: string, pos: int, x: int, y: int, pred: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    requires pred == -1 || pred == 0 || pred == 1
    ensures CountTransitionsHelper(s, pos, x, y, pred) >= 0
    ensures CountTransitionsHelper(s, pos, x, y, pred) <= |s| - pos
    decreases |s| - pos
{
    if pos == |s| then 0
    else
        var newX := if s[pos] == 'U' then x else x + 1;
        var newY := if s[pos] == 'U' then y + 1 else y;

        if newX == newY then
            CountTransitionsHelper(s, pos + 1, newX, newY, pred)
        else
            var cur := if newX > newY then 0 else 1;
            var transition := if cur != pred && pred != -1 then 1 else 0;
            transition + CountTransitionsHelper(s, pos + 1, newX, newY, cur)
}

// <vc-helpers>
function CountXs(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountXs(s, pos_end) >= 0
    ensures CountXs(s, pos_end) <= pos_end
{
    if pos_end == 0 then 0
    else
        var x_prev := CountXs(s, pos_end - 1);
        if s[pos_end - 1] == 'U' then x_prev else x_prev + 1
}

function CountYs(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountYs(s, pos_end) >= 0
    ensures CountYs(s, pos_end) <= pos_end
{
    if pos_end == 0 then 0
    else
        var y_prev := CountYs(s, pos_end - 1);
        if s[pos_end - 1] == 'U' then y_prev + 1 else y_prev
}

function GetPred(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures GetPred(s, pos_end) == -1 || GetPred(s, pos_end) == 0 || GetPred(s, pos_end) == 1
{
    if pos_end == 0 then -1
    else
        var x_cur := CountXs(s, pos_end);
        var y_cur := CountYs(s, pos_end);
        if x_cur == y_cur then GetPred(s, pos_end - 1) // Recurse to find the last non-equal pred
        else if x_cur > y_cur then 0
        else 1
}

function GetPrevPred(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures GetPrevPred(s, pos_end) == -1 || GetPrevPred(s, pos_end) == 0 || GetPrevPred(s, pos_end) == 1
{
    if pos_end == 0 then -1
    else
        var x_prev := CountXs(s, pos_end - 1);
        var y_prev := CountYs(s, pos_end - 1);
        if x_prev == y_prev then GetPrevPred(s, pos_end - 1)
        else if x_prev > y_prev then 0
        else 1
}


function CountTransitionsUpto(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountTransitionsUpto(s, pos_end) >= 0
    ensures CountTransitionsUpto(s, pos_end) <= pos_end
{
    if pos_end == 0 then 0
    else
        var prev_transitions := CountTransitionsUpto(s, pos_end - 1);
        var prev_x := CountXs(s, pos_end - 1);
        var prev_y := CountYs(s, pos_end - 1);
        var prev_pred_val := GetPred(s, pos_end - 1);

        var newX_after_current_char := if s[pos_end - 1] == 'U' then prev_x else prev_x + 1;
        var newY_after_current_char := if s[pos_end - 1] == 'U' then prev_y + 1 else prev_y;

        if newX_after_current_char == newY_after_current_char then
            prev_transitions
        else
            var cur := if newX_after_current_char > newY_after_current_char then 0 else 1;
            if cur != prev_pred_val && prev_pred_val != -1 then
                prev_transitions + 1
            else
                prev_transitions
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures result >= 0
    ensures result <= n
    ensures n == 0 ==> result == 0
    ensures result == CountKingdomTransitions(s)
// </vc-spec>
// <vc-code>
{
    if n == 0 then
        return 0;
    else
        var x := 0;
        var y := 0;
        var pred := -1; // -1: undefined, 0: x > y, 1: y > x
        var transitions := 0;

        var i := 0;
        while i < n
            invariant 0 <= i <= n
            invariant x == CountXs(s, i)
            invariant y == CountYs(s, i)
            invariant pred == GetPred(s, i)
            invariant transitions == CountTransitionsUpto(s, i)
        {
            var newX := x;
            var newY := y;
            if s[i] == 'U' then
                newY := y + 1;
            else
                newX := x + 1;

            if newX == newY then
                // pred stays the same as before this step
                // No transition counted
                x := newX;
                y := newY;
            else
                var cur := if newX > newY then 0 else 1; // current kingdom
                if cur != pred && pred != -1 then
                    transitions := transitions + 1;
                pred := cur; // update pred for the next iteration
                x := newX;
                y := newY;
            i := i + 1;
        }
        return transitions;
    }
}
// </vc-code>

