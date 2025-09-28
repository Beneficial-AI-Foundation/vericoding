// <vc-preamble>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected sequence initialization syntax. */
function ComputeSchedule(n: int, k: int, a: seq<int>): (finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures |finalSchedule| == n
    ensures forall i :: 0 <= i < n ==> finalSchedule[i] >= a[i]
    ensures forall i :: 0 <= i < n - 1 ==> finalSchedule[i] + finalSchedule[i+1] >= k
{
    var schedule_seq: seq<int> := (seq<int>(n, _ => 0));
    schedule_seq := schedule_seq[0 := a[0]];

    if n > 1 {
        schedule_seq := schedule_seq[1 := max(a[1], k - schedule_seq[0])];
        var i := 2;
        while i < n
            invariant 0 <= i <= n
            invariant forall j :: 0 <= j < i ==> schedule_seq[j] >= a[j]
            invariant forall j :: 0 <= j < i - 1 ==> schedule_seq[j] + schedule_seq[j+1] >= k
        {
            schedule_seq := schedule_seq[i := max(a[i], k - schedule_seq[i-1])];
            i := i + 1;
        }
    }
    return schedule_seq;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed. */
{
    var schedule := ComputeSchedule(n, k, a);
    additionalWalks := sum(schedule) - sum(a);
    finalSchedule := schedule;
}
// </vc-code>
