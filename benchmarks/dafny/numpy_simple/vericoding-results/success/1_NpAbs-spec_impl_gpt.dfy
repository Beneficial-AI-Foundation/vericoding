// <vc-preamble>
function AbsInt(x: int): int
{
    if x < 0 then -x else x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove AbsInt is non-negative */
lemma AbsIntNonNeg(x: int)
  ensures AbsInt(x) >= 0
{
  if x < 0 {
    // AbsInt(x) == -x and therefore >= 0
  } else {
    // AbsInt(x) == x and therefore >= 0
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
  /* code modified by LLM (iteration 2): implement absolute value mapping with proper invariants and no null comparisons */
  result := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result.Length == a.Length
    invariant forall j :: 0 <= j < i ==> result[j] == AbsInt(a[j])
    invariant forall j :: 0 <= j < i ==> result[j] >= 0
    decreases a.Length - i
  {
    AbsIntNonNeg(a[i]);
    result[i] := AbsInt(a[i]);
    i := i + 1;
  }
}
// </vc-code>
