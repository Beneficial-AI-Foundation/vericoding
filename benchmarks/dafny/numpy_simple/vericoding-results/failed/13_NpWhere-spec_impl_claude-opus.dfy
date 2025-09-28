// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 5): Fixed parse error - removed method signature, keeping only method bodies */
  result := new int[condition.Length];
  var i := 0;
  while i < condition.Length
    invariant 0 <= i <= condition.Length
    invariant forall j :: 0 <= j < i ==> result[j] == if condition[j] then x[j] else y[j]
  {
    if condition[i] {
      result[i] := x[i];
    } else {
      result[i] := y[i];
    }
    i := i + 1;
  }
}

method WhereWithTransform(arr: array<int>) returns (result: array<int>)
{
  result := new int[arr.Length];
}
// </vc-code>
