// <vc-preamble>
function AbsInt(x: int): int
{
    if x < 0 then -x else x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proof that AbsInt is non-negative */
lemma AbsInt_nonneg(x: int)
  ensures AbsInt(x) >= 0
{
  if x < 0 {
    assert AbsInt(x) == -x;
    assert -x >= 0;
  } else {
    assert AbsInt(x) == x;
    assert x >= 0;
  }
}

// </vc-helpers>

// <vc-spec>
method Abs(a: array<int>) returns (result: array<int>)
    ensures 
        result.Length == a.Length &&
        (forall i :: 0 <= i < a.Length ==> result[i] == AbsInt(a[i])) &&
        (forall i :: 0 <= i < result.Length ==> result[i] >= 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement Abs by creating result array and filling with AbsInt values */
  var n := a.Length;
  var res := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> res[j] == AbsInt(a[j])
    invariant forall j :: 0 <= j < i ==> res[j] >= 0
  {
    if a[i] < 0 {
      res[i] := -a[i];
    } else {
      res[i] := a[i];
    }
    assert res[i] == AbsInt(a[i]);
    AbsInt_nonneg(a[i]);
    assert res[i] >= 0;
    i := i + 1;
  }
  result := res;
}

// </vc-code>
