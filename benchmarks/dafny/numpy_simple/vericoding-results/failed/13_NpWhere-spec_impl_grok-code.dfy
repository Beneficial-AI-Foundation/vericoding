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
/* code modified by LLM (iteration 5): fixed loop bounds and added loop invariants to satisfy postconditions */

method WhereFn_impl(condition: array<bool>, x: array<int>, y: array<int>) returns (result: array<int>)
    requires
        condition.Length == x.Length &&
        x.Length == y.Length
    ensures
        result.Length == condition.Length &&
        forall i :: 0 <= i < result.Length ==>
            result[i] == if condition[i] then x[i] else y[i]
{
  result := new int[condition.Length];
  if condition.Length > 0 {
    for i := 0 to condition.Length - 1
      invariant 0 <= i <= condition.Length
      invariant forall j :: 0 <= j < i ==> result[j] == if condition[j] then x[j] else y[j]
    {
      result[i] := if condition[i] then x[i] else y[i];
    }
  }
}

method WhereWithTransform_impl(arr: array<int>) returns (result: array<int>)
    requires arr.Length >= 0
    ensures
        result.Length == arr.Length
{
  result := new int[arr.Length];
  if arr.Length > 0 {
    for i := 0 to arr.Length - 1
    {
      result[i] := arr[i];
    }
  }
}
// </vc-code>
