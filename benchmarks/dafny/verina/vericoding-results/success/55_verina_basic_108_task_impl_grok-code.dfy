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
  /* code modified by LLM (iteration 3): added loop invariants to prove postconditions */
  var balance := new int[operations.Length + 1];
  balance[0] := 0;
  var wentBelow := false;
  var i := 0;
  while i < operations.Length
    invariant 0 <= i <= operations.Length
    invariant forall k :: 0 <= k < i ==> balance[k+1] == balance[k] + operations[k]
    invariant balance[0] == 0
    invariant wentBelow == (exists j :: 1 <= j <= i && balance[j] < 0)
  {
    balance[i + 1] := balance[i] + operations[i];
    if balance[i + 1] < 0 {
      wentBelow := true;
    }
    i := i + 1;
  }
  result := (balance, wentBelow);
}
// </vc-code>
