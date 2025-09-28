// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed for this iteration based on error */
function ClipSingle(value: real, min_val: real, max_val: real): real
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
/* code modified by LLM (iteration 5): Corrected loop bounds to handle empty arrays and fixed 'result' assignment. */
{
  var new_arr: seq<real> := arr;
  for i := 0 to |arr|
    invariant 0 <= i <= |arr|
    invariant |new_arr| == |arr|
    invariant forall j :: 0 <= j < i ==> (new_arr[j] == ClipSingle(arr[j], min_val, max_val))
  {
    if i < |arr| {
      new_arr := new_arr[i := ClipSingle(arr[i], min_val, max_val)];
    }
  }
  result := new_arr;
}
// </vc-code>
