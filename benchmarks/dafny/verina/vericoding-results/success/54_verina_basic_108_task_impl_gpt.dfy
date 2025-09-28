// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple addition function */
function Sum(a: int, b: int): int {
  a + b
}

/* helper modified by LLM (iteration 2): predicate to check negativity */
predicate IsNegative(x: int)
{
  x < 0
}
// </vc-helpers>

// <vc-spec>
method BelowZero(operations: array<int>) returns (result: (array<int>, bool))
    ensures
        result.0.Length == operations.Length + 1
    ensures
        result.0[0] == 0
    ensures
        forall i :: 0 <= i < operations.Length ==> result.0[i + 1] == result.0[i] + operations[i]
    ensures
        result.1 == (exists i :: 1 <= i < result.0.Length && result.0[i] < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement prefix sums and track if any cumulative sum goes below zero using loop invariants */
  var n := operations.Length;
  var arr := new int[n + 1];
  arr[0] := 0;
  var i := 0;
  var everNeg := false;
  while i < n
    invariant 0 <= i <= n
    invariant i < arr.Length
    invariant arr.Length == n + 1
    invariant arr[0] == 0
    invariant forall k :: 0 <= k < i ==> arr[k + 1] == arr[k] + operations[k]
    invariant everNeg ==> (exists j :: 1 <= j <= i && arr[j] < 0)
    invariant !everNeg ==> (forall j :: 1 <= j <= i ==> arr[j] >= 0)
    decreases n - i
  {
    arr[i + 1] := arr[i] + operations[i];
    if arr[i + 1] < 0 {
      everNeg := true;
    }
    i := i + 1;
  }
  result := (arr, everNeg);
}
// </vc-code>
