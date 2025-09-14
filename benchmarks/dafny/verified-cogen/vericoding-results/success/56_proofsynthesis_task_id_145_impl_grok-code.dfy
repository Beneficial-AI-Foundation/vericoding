// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
method GetMin(arr: array<int>) returns (min: int)
requires arr.Length > 0
ensures forall i :: 0 <= i < arr.Length ==> arr[i] >= min
/* helper modified by LLM (iteration 4): Fixed loop to use while for Length=1 case and strengthened invariant */
{
  var i := 1;
  min := arr[0];
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] >= min
  {
    if arr[i] < min {
      min := arr[i];
    }
    i := i + 1;
  }
}

method GetMax(arr: array<int>) returns (max: int)
requires arr.Length > 0
ensures forall i :: 0 <= i < arr.Length ==> arr[i] <= max
/* helper modified by LLM (iteration 4): Fixed loop to use while for Length=1 case and strengthened invariant */
{
  var i := 1;
  max := arr[0];
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] <= max
  {
    if arr[i] > max {
      max := arr[i];
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method MaxDifference(arr: array<int>) returns (diff: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] - arr[j] <= diff
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): No changes */
{
  var min_val := GetMin(arr);
  var max_val := GetMax(arr);
  diff := max_val - min_val;
}
// </vc-code>
