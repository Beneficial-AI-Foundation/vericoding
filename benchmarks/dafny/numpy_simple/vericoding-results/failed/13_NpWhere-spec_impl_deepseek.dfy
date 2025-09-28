// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AllIndicesInRange(arr: array<int>, low: int, high: int): bool
  reads arr
  requires 0 <= low <= high <= arr.Length
{
  if low == high then
    true
  else
    arr[low] >= 0 && arr[low] <= arr.Length && AllIndicesInRange(arr, low + 1, high)
}

lemma AllIndicesInRangeMaintainsProperty(arr: array<int>, low: int, high: int, i: int)
  requires 0 <= low <= i < high <= arr.Length
  requires AllIndicesInRange(arr, low, high)
  ensures 0 <= arr[i] <= arr.Length
{
  if low == i {
    // Base case: the property holds for arr[i]
  } else {
    AllIndicesInRangeMaintainsProperty(arr, low + 1, high, i);
  }
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
  /* code modified by LLM (iteration 5): Removed extra opening brace to fix parse error */
  result := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result.Length == arr.Length
    invariant forall j :: 0 <= j < i ==> result[j] == if arr[j] >= 0 && arr[j] <= arr.Length then arr[j] else 0
  {
    if arr[i] >= 0 && arr[i] <= arr.Length {
      result[i] := arr[i];
    } else {
      result[i] := 0;
    }
    i := i + 1;
  }
}
// </vc-code>
