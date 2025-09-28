// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ElementInRange predicate to remove circular dependencies */
predicate ElementInRange(vals_1: array<int>, vals_2: array<int>, i: int)
  reads vals_1, vals_2
  requires 0 <= i < vals_1.Length
  requires vals_1.Length == vals_2.Length
{
  vals_1[i] < 1000 && vals_2[i] < 1000
}

/* helper modified by LLM (iteration 5): Added lemma to prove array element bounds */
lemma ArrayElementBoundsLemma(vals: array<int>, idx: int)
  requires 0 <= idx < vals.Length
  requires forall i :: 0 <= i < vals.Length ==> vals[i] < 1000
  ensures vals[idx] < 1000
{
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
/* code modified by LLM (iteration 5): Fixed verification by proving array element bounds */
{
  var i := 0;
  while i < vals_1.Length
    invariant 0 <= i <= vals_1.Length
    invariant forall idx :: 0 <= idx < i ==> (
        (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
        (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
        (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
    )
    invariant forall idx :: 0 <= idx < i ==> ElementInRange(vals_1, vals_2, idx)
  {
    ArrayElementBoundsLemma(vals_1, i);
    ArrayElementBoundsLemma(vals_2, i);
    assert ElementInRange(vals_1, vals_2, i);
    if conds_1[i] {
      if conds_2[i] {
        avgs[i] := (vals_1[i] + vals_2[i]) / 2;
      } else {
        avgs[i] := vals_1[i];
      }
    } else {
      if conds_2[i] {
        avgs[i] := vals_2[i];
      }
    }
    i := i + 1;
  }
}
// </vc-code>
