// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ClipElem(x: real, min_val: real, max_val: real): real {
  if min_val <= max_val then
    (if x < min_val then min_val else if x > max_val then max_val else x)
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
  var n := |arr|;
  var res := arr;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == |arr|
    invariant forall k :: 0 <= k < i ==> (
      if min_val <= max_val then
        (if arr[k] < min_val then res[k] == min_val
         else if arr[k] > max_val then res[k] == max_val
         else res[k] == arr[k])
      else
        res[k] == max_val
    )
    decreases n - i
  {
    var v := arr[i];
    var rv: real;
    if min_val <= max_val {
      if v < min_val {
        rv := min_val;
      } else if v > max_val {
        rv := max_val;
      } else {
        rv := v;
      }
    } else {
      rv := max_val;
    }
    res := res[i := rv];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
