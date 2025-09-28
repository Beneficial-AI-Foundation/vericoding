// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): choose between two ints based on condition */
function WhereSelect(cond: bool, a: int, b: int): int {
  if cond then a else b
}

// </vc-helpers>

// <vc-spec>
method WhereFn(condition: array<bool>, x: array<int>, y: array<int>) returns (result: array<int>)
    requires 
        condition.Length == x.Length &&
        x.Length == y.Length
    ensures 
        result.Length == condition.Length &&
        forall i :: 0 <= i < result.Length ==> 
            result[i] == if condition[i] then x[i] else y[i]
{
    assume {:axiom} false;
}

method WhereWithTransform(arr: array<int>) returns (result: array<int>)
    requires arr.Length >= 0
    ensures 
        result.Length == arr.Length
{
    assume {:axiom} false;
}
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement element-wise selection using helper */
  var n := condition.Length;
  result := new int[n];
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == if condition[j] then x[j] else y[j]
  {
    result[i] := WhereSelect(condition[i], x[i], y[i]);
    i := i + 1;
  }
}

{
  /* code modified by LLM (iteration 5): copy input array to result preserving length */
  var n := arr.Length;
  result := new int[n];
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == arr[j]
  {
    result[i] := arr[i];
    i := i + 1;
  }
}

// </vc-code>
