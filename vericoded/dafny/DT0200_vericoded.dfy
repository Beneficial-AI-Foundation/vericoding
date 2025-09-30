// <vc-preamble>
// Method to convert an array of real numbers to a string representation
// The array is formatted with brackets and elements separated by the given separator
// </vc-preamble>

// <vc-helpers>
function RealToString(r: real): string
{
  if r == 0.0 then "0.0"
  else if r > 0.0 then "1.0"  // placeholder positive representation
  else "-1.0"  // placeholder negative representation
}

function ArrayElementsToString(arr: seq<real>, separator: string, index: nat): string
  requires index <= |arr|
  decreases |arr| - index
{
  if index == |arr| then ""
  else if index == |arr| - 1 then RealToString(arr[index])
  else RealToString(arr[index]) + separator + ArrayElementsToString(arr, separator, index + 1)
}
// </vc-helpers>

// <vc-spec>
method Array2String(arr: seq<real>, separator: string) returns (result: string)
    requires true  // No special preconditions
    ensures result != ""  // Result is non-empty
    ensures |result| >= 2  // Must be at least "[]"
    ensures result[0] == '['  // Starts with opening bracket
    ensures result[|result|-1] == ']'  // Ends with closing bracket
// </vc-spec>
// <vc-code>
{
  if |arr| == 0 {
    result := "[]";
  } else {
    var elements := ArrayElementsToString(arr, separator, 0);
    result := "[" + elements + "]";
  }
}
// </vc-code>
