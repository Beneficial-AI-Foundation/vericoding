// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  if min_val > max_val {
    result := seq(|arr|, i => max_val);
  } else {
    result := seq(|arr|, i requires 0 <= i < |arr| => 
      if arr[i] < min_val then min_val
      else if arr[i] > max_val then max_val
      else arr[i]);
  }
}
// </vc-code>
