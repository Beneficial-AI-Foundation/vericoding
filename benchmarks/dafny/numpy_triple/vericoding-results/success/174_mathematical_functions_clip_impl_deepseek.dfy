// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

  // Helper predicate to determine clipping behavior
  predicate IsOrderedBounds(min_val: real, max_val: real)
    ensures IsOrderedBounds(min_val, max_val) <==> min_val <= max_val
  {
    min_val <= max_val
  }

  // Helper function to clip a single value
  function ClipValue(value: real, min_val: real, max_val: real): (clipped: real)
    ensures (clipped >= min_val && clipped <= max_val) || !IsOrderedBounds(min_val, max_val)
    ensures IsOrderedBounds(min_val, max_val) ==> (
      if value < min_val then clipped == min_val
      else if value > max_val then clipped == max_val
      else clipped == value
    )
    ensures !IsOrderedBounds(min_val, max_val) ==> clipped == max_val
  {
    if min_val <= max_val then
      if value < min_val then min_val
      else if value > max_val then max_val
      else value
    else
      max_val
  }

// </vc-helpers>

// <vc-spec>
method Clip(arr: seq<real>, min_val: real, max_val: real) returns (result: seq<real>)
  // Precondition: no special requirements (handles all real number inputs)
  
  // Postcondition: result preserves input array length
  ensures |result| == |arr|
  
  // Postcondition: each element is properly clipped according to the interval bounds
  ensures forall i :: 0 <= i < |arr| ==> (
    if min_val <= max_val then
      // Normal clipping behavior when min_val <= max_val
      (if arr[i] < min_val then result[i] == min_val
       else if arr[i] > max_val then result[i] == max_val
       else result[i] == arr[i])
    else 
      // Special case: when min_val > max_val, all values become max_val
      result[i] == max_val
  )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by adding parentheses */
  result := [];
  var i := 0;

  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (
      if min_val <= max_val then
        (if arr[j] < min_val then result[j] == min_val
         else if arr[j] > max_val then result[j] == max_val
         else result[j] == arr[j])
      else result[j] == max_val
    )
  {
    result := result + [ClipValue(arr[i], min_val, max_val)];
    i := i + 1;
  }
}
// </vc-code>
