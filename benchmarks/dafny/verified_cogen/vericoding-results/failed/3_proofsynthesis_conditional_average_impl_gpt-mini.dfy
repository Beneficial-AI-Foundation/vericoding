// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to bound sum under 2000 */
predicate IsSmall(x: int) { x < 1000 }

lemma SumLessThanTwoThousand(a: int, b: int)
  requires a < 1000 && b < 1000
  ensures a + b < 2000
{
  // From a < 1000 we get a + b < 1000 + b
  assert a + b < 1000 + b;
  // From b < 1000 we get 1000 + b < 1000 + 1000
  assert 1000 + b < 1000 + 1000;
  // 1000 + 1000 equals 2000
  assert 1000 + 1000 == 2000;
  // Combine to conclude a + b < 2000
  assert a + b < 2000;
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
{
  /* code modified by LLM (iteration 5): direct per-index assignments using arrays to avoid local alias issues */
  var n := vals_1.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==>
      ((conds_1[j] && conds_2[j] ==> avgs[j] == (vals_1[j] + vals_2[j]) / 2) &&
       (conds_1[j] && !conds_2[j] ==> avgs[j] == vals_1[j]) &&
       (!conds_1[j] && conds_2[j] ==> avgs[j] == vals_2[j]))
  {
    if conds_1[i] {
      if conds_2[i] {
        avgs[i] := (vals_1[i] + vals_2[i]) / 2;
      } else {
        avgs[i] := vals_1[i];
      }
    } else {
      avgs[i] := vals_2[i];
    }
    i := i + 1;
  }
}

// </vc-code>
