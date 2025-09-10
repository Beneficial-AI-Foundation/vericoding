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

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
  // initialize mutable array for final schedule
  var b := new int[n];
  // use the output variable additionalWalks
  additionalWalks := 0;
  // first element stays at least a[0]
  b[0] := a[0];
  // processed is how many elements of b have been fixed (1..n)
  var processed := 1;
  // invariant: processed elements fixed and properties hold on them
  while processed < n
    invariant 1 <= processed <= n
    invariant forall t :: 0 <= t < processed ==> b[t] >= a[t]
    invariant forall t :: 0 <= t < processed - 1 ==> b[t] + b[t+1] >= k
    invariant additionalWalks == sum(b[..processed]) - sum(a[..processed])
    invariant additionalWalks >= 0
    decreases n - processed
  {
    var need := k - b[processed - 1];
    if need < a[processed] {
      b[processed] := a[processed];
    } else {
      b[processed] := need;
    }
    // update additionalWalks to account for the increase at index processed
    additionalWalks := additionalWalks + (b[processed] - a[processed]);
    processed := processed + 1;
  }

  // set the output sequence
  finalSchedule := b[..];
}
// </vc-code>

