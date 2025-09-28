// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [removed unused GetClippedElement helper] */
function clip_one(x: real, min_val: real, max_val: real): real
{
  if min_val <= max_val then
    if x < min_val then min_val
    else if x > max_val then max_val
    else x
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
  /* code modified by LLM (iteration 3): [use a while loop for explicit, verifiable sequence construction] */
  var i: nat := 0;
  result := [];
  while i < |arr|
    invariant |result| == i
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < i ==> result[j] == clip_one(arr[j], min_val, max_val)
  {
    var clipped_val := clip_one(arr[i], min_val, max_val);
    result := result + [clipped_val];
    i := i + 1;
  }
}
// </vc-code>
