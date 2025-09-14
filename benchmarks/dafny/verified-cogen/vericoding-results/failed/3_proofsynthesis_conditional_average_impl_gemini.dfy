// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
{
  /* code modified by LLM (iteration 5): [Rewrote loop invariant using if-then-else and aligned body logic.] */
  var i := 0;
  while i < vals_1.Length
    invariant 0 <= i <= vals_1.Length
    invariant forall idx :: 0 <= idx < i ==>
        if conds_1[idx] && conds_2[idx] then avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2
        else if conds_1[idx] then avgs[idx] == vals_1[idx]
        else avgs[idx] == vals_2[idx]
    modifies avgs
  {
    if conds_1[i] && conds_2[i] {
      avgs[i] := (vals_1[i] + vals_2[i]) / 2;
    } else if conds_1[i] {
        avgs[i] := vals_1[i];
    } else {
      assert conds_2[i]; // from requires clause `conds_1[i] || conds_2[i]`
      avgs[i] := vals_2[i];
    }
    i := i + 1;
  }
}
// </vc-code>
