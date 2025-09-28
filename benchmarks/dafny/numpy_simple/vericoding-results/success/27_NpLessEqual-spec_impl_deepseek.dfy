// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ArrayEqualLength(a: array<int>, b: array<int>): bool
{
  a.Length == b.Length
}

predicate ValidIndices(a: array<int>, i: int)
{
  0 <= i < a.Length
}
// </vc-helpers>

// <vc-spec>
method LessEqual(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] <= b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): removed verification bypass and implemented proper array comparison */
  result := new bool[a.Length];
  var j := 0;
  while j < a.Length
    invariant j <= a.Length
    invariant forall k :: 0 <= k < j ==> result[k] == (a[k] <= b[k])
  {
    result[j] := a[j] <= b[j];
    j := j + 1;
  }
}
// </vc-code>
