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
                // Still on the central line, no kingdom established yet or back to central
                // The 'pred' value should be maintained if it was already established,
                // or remain -1 if not.
                // However, the rule simplifies: if we hit the centerline again, we don't count a transition *now*.
                // The 'pred' value for the *next* step (pred of the current system) effectively becomes -1
                // for the purpose of counting transitions from this point on, if we *leave* the centerline.
                // But the definition of 'pred' is for (x, y) relative to the *previous* state.
                // Let's stick to the function's logic. If newX == newY, 'pred' remains unchanged for the recursive call.
                // This means the effective 'pred' for newX==newY case is the 'pred' from the *previous* step,
                // and it doesn't count a transition.
                // So, `pred` needs to be updated relative to the new (x,y) if they are not equal.
                // In our iterative approach, the `pred` we carry forward is the state of the *previous* step.

                // When newX == newY, the effective 'pred' for the *next* iteration (i.e., state after this step)
                // should be related to this (newX, newY) being on the line.
                // The original function passed the 'pred' value as the state *before* this step.
                // 'cur' is the state *after* this step.
                // So, if newX == newY, 'pred' is simply carried over to the next loop iteration.
                // This simulates 'CountTransitionsHelper(s, pos + 1, newX, newY, pred)'
                // The 'pred' passed to the next iteration will be the *current* 'pred'.
                // If it was -1, it stays -1. If it was 0 or 1, it stays 0 or 1.
                // The only case 'pred' actually changes is *when* we are not on the center line.
                // No need to change 'pred' here.
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

// Auxiliary functions to prove invariants, mirroring CountTransitionsHelper's logic
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

// Helper to get the 'pred' value after 'pos_end' moves, effectively the 'cur' value for the (x,y) at pos_end
// This describes the "kingdom" at step 'pos_end', or -1 if on the center line or not yet diverged.
function GetPred(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures GetPred(s, pos_end) == -1 || GetPred(s, pos_end) == 0 || GetPred(s, pos_end) == 1
{
    if pos_end == 0 then -1
    else
        var x_cur := CountXs(s, pos_end);
        var y_cur := CountYs(s, pos_end);
        if x_cur == y_cur then GetPred(s, pos_end - 1) // On the center line, previous 'pred' applies conceptually. Or, based on the function, this implies 'pred' is not updated by a center line crossing.
                                                    // This must match the iterative logic. If newX == newY, `pred` is NOT updated. So for a given `i`, `pred` is the `GetPred` of the state just BEFORE the current `i`.
                                                    // Let's refine this invariant. `pred` in the loop is the 'pred' from the previous step (i-1).
                                                    // In the loop it is 'pred := cur'. So at `i`, `pred` represents the kingdom at `i-1`.
                                                    // No, `pred` in loop becomes `cur` for the *next* iteration. So `pred` at start of iteration `i` is the kingdom from `i-1`.
                                                    // This means `pred` at `i` is `GetPredAtI(s, i-1)`.
        else if x_cur > y_cur then 0
        else 1
}

// Let's define the pred value *as it exists at iteration i*, which is based on the kingdom from step i-1
function GetPredAtStartOfIteration(s: string, k: int): int
    requires 0 <= k <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures GetPredAtStartOfIteration(s, k) == -1 || GetPredAtStartOfIteration(s, k) == 0 || GetPredAtStartOfIteration(s, k) == 1
{
    // This function calculates what the `pred` variable *would be* at the start of iteration `k`.
    // This value is determined by the state at `k-1` (after processing `s[k-1]`).
    if k == 0 then -1 // Initial `pred`
    else
        var x_prev := CountXs(s, k - 1);
        var y_prev := CountYs(s, k - 1);
        var newX_at_k_minus_1 := if s[k-1] == 'U' then x_prev else x_prev + 1;
        var newY_at_k_minus_1 := if s[k-1] == 'U' then y_prev + 1 else y_prev;

        if newX_at_k_minus_1 == newY_at_k_minus_1 then
            GetPredAtStartOfIteration(s, k - 1) // This is the subtle point. What `pred` value means when back on center line.
                                                // The iterative implementation means: if newX == newY, `pred` is unchanged.
                                                // So, the `pred` value at this specific state `k` is simply whatever `pred` was at `k-1`.
                                                // This holds true recursively.
        else if newX_at_k_minus_1 > newY_at_k_minus_1 then 0
        else 1
}

// Function to calculate transitions up to (but not including) position `pos_end`.
// This represents the `transitions` variable's value at the start of iteration `pos_end`.
function CountTransitionsUpto(s: string, pos_end: int): int
    requires 0 <= pos_end <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountTransitionsUpto(s, pos_end) >= 0
    ensures CountTransitionsUpto(s, pos_end) <= pos_end
{
    if pos_end == 0 then 0
    else
        var prev_transitions := CountTransitionsUpto(s, pos_end - 1);
        var pred_at_prev_step := GetPredAtStartOfIteration(s, pos_end - 1); // pred variable value *before* processing s[pos_end-1]

        var x_current_at_prev_step := CountXs(s, pos_end - 1);
        var y_current_at_prev_step := CountYs(s, pos_end - 1);

        var newX_after_prev_step := if s[pos_end - 1] == 'U' then x_current_at_prev_step else x_current_at_prev_step + 1;
        var newY_after_prev_step := if s[pos_end - 1] == 'U' then y_current_at_prev_step + 1 else y_current_at_prev_step;

        if newX_after_prev_step == newY_after_prev_step then
            prev_transitions // No new transition, pred is not updated by this step
        else
            var cur_after_prev_step := if newX_after_prev_step > newY_after_prev_step then 0 else 1;
            if cur_after_prev_step != GetPredAtStartOfIteration(s, pos_end-1)  && GetPredAtStartOfIteration(s, pos_end-1) != -1 then
                prev_transitions + 1
            else
                prev_transitions
}
// </vc-code>

