// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 3): Fixed loop bounds and added invariants to verify postconditions */
  var arr := new int[operations.Length + 1];
  arr[0] := 0;
  var i := 0;
  while i < operations.Length
    invariant 0 <= i && i <= operations.Length
    invariant forall k :: 0 <= k < i ==> arr[k + 1] == arr[k] + operations[k]
    invariant arr[0] == 0
  {
    arr[i + 1] := arr[i] + operations[i];
    i := i + 1;
  }
  var belowZero := false;
  var j := 1;
  while j <= operations.Length
    invariant 1 <= j <= operations.Length + 1
    invariant belowZero == (exists k :: 1 <= k < j && arr[k] < 0)
  {
    if arr[j] < 0 {
      belowZero := true;
    }
    j := j + 1;
  }
  result := (arr, belowZero);
}
// </vc-code>
