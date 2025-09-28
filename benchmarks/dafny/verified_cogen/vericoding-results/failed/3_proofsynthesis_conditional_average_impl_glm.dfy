// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): helper function to calculate conditional average */
function CalculateAverage(v1: int, v2: int, c1: bool, c2: bool): int {
  if c1 && c2 then (v1 + v2) / 2
  else if c1 then v1
  else v2
}
// </vc-helpers>

// <vc-spec>
method ConditionalAverage(vals_1: array<int>, vals_2: array<int>, conds_1: array<bool>, conds_2: array<bool>, avgs: array<int>)
    requires vals_1.Length == vals_2.Length
    requires vals_1.Length == conds_1.Length  
    requires vals_1.Length == conds_2.Length
    requires avgs.Length == vals_1.Length
    requires forall idx :: 0 <= idx < vals_1.Length ==> conds_1[idx] || conds_2[idx]
    requires forall idx :: 0 <= idx < vals_1.Length ==> vals_1[idx] < 1000
    requires forall idx :: 0 <= idx < vals_2.Length ==> vals_2[idx] < 1000
    modifies avgs
    ensures forall idx :: 0 <= idx < vals_1.Length ==> (
        (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
        (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
        (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
    )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added ghost variable to track initial array and used while-loop */
{
  ghost var initial_avgs := avgs[..];
  var idx := 0;
  while idx < vals_1.Length
    invariant 0 <= idx <= vals_1.Length
    invariant forall i :: 0 <= i < idx ==> avgs[i] == CalculateAverage(vals_1[i], vals_2[i], conds_1[i], conds_2[i])
    invariant forall i :: idx <= i < vals_1.Length ==> avgs[i] == initial_avgs[i]
  {
    avgs[idx] := CalculateAverage(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx]);
    idx := idx + 1;
  }
}
// </vc-code>
