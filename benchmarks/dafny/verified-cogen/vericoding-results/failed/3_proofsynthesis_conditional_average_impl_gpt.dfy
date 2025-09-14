// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): deterministic combination based on two conditions */
function CombinedValue(v1: int, v2: int, c1: bool, c2: bool): int {
  if c1 && c2 then (v1 + v2) / 2
  else if c1 then v1
  else v2
}
/* helper modified by LLM (iteration 5): lemma connecting CombinedValue with case analysis */
lemma CombinedValueAgree(v1: int, v2: int, c1: bool, c2: bool)
  ensures (c1 && c2 ==> CombinedValue(v1, v2, c1, c2) == (v1 + v2) / 2)
  ensures (c1 && !c2 ==> CombinedValue(v1, v2, c1, c2) == v1)
  ensures (!c1 && c2 ==> CombinedValue(v1, v2, c1, c2) == v2)
{
  if c1 && c2 {
    assert CombinedValue(v1, v2, c1, c2) == (v1 + v2) / 2;
  } else if c1 && !c2 {
    assert CombinedValue(v1, v2, c1, c2) == v1;
  } else {
    if c2 {
      assert CombinedValue(v1, v2, c1, c2) == v2;
    }
  }
}
/* helper modified by LLM (iteration 5): arithmetic lemma to conclude idx == i from bounds */
lemma IndexIsI(i: int, idx: int)
  requires i <= idx < i + 1
  ensures idx == i
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
{
  /* code modified by LLM (iteration 5): implement loop and strengthen invariant preservation with quantified assertion; discharge postcondition via helper lemma */
  var n := vals_1.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant vals_1.Length == n && vals_2.Length == n && conds_1.Length == n && conds_2.Length == n && avgs.Length == n
    invariant forall idx :: 0 <= idx < i ==> avgs[idx] == CombinedValue(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx])
    decreases n - i
  {
    avgs[i] := CombinedValue(vals_1[i], vals_2[i], conds_1[i], conds_2[i]);
    assert forall idx :: 0 <= idx < i + 1 ==> avgs[idx] == CombinedValue(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx]) by {
      forall idx | 0 <= idx < i + 1
        ensures avgs[idx] == CombinedValue(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx])
      {
        if idx < i {
          // from invariant
        } else {
          IndexIsI(i, idx);
          assert idx == i;
          assert avgs[idx] == avgs[i];
          assert avgs[i] == CombinedValue(vals_1[i], vals_2[i], conds_1[i], conds_2[i]);
        }
      }
    }
    i := i + 1;
  }
  assert i == n;
  assert forall idx :: 0 <= idx < n ==> (
    (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
    (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
    (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
  ) by {
    forall idx | 0 <= idx < n
      ensures (conds_1[idx] && conds_2[idx] ==> avgs[idx] == (vals_1[idx] + vals_2[idx]) / 2) &&
              (conds_1[idx] && !conds_2[idx] ==> avgs[idx] == vals_1[idx]) &&
              (!conds_1[idx] && conds_2[idx] ==> avgs[idx] == vals_2[idx])
    {
      assert idx < i;
      assert avgs[idx] == CombinedValue(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx]);
      CombinedValueAgree(vals_1[idx], vals_2[idx], conds_1[idx], conds_2[idx]);
    }
  }
}

// </vc-code>
