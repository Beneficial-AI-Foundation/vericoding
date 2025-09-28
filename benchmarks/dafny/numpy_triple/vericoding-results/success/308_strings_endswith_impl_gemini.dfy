// <vc-preamble>
// Method to check if strings in array end with given suffixes
// </vc-preamble>

// <vc-helpers>
function StringEndsWith(s: string, suffix: string): bool
{
  |suffix| <= |s| && s[|s| - |suffix|..] == suffix
}
// </vc-helpers>

// <vc-spec>
method endswith(a: seq<string>, suffix: seq<string>) returns (result: seq<bool>)
    // Input sequences must have the same length
    requires |a| == |suffix|
    // Output sequence has the same length as inputs
    ensures |result| == |a|
    // Main specification: result matches endsWith check for each pair
    ensures forall i :: 0 <= i < |result| ==>
        result[i] == (|suffix[i]| <= |a[i]| && 
                     a[i][|a[i]| - |suffix[i]|..] == suffix[i])
    // Mathematical property: if result is true, suffix appears at the end
    ensures forall i :: 0 <= i < |result| && result[i] ==>
        |suffix[i]| <= |a[i]| &&
        a[i][|a[i]| - |suffix[i]|..] == suffix[i]
    // Mathematical property: if result is false, suffix does not appear at the end  
    ensures forall i :: 0 <= i < |result| && !result[i] ==>
        |suffix[i]| > |a[i]| ||
        (|suffix[i]| <= |a[i]| && a[i][|a[i]| - |suffix[i]|..] != suffix[i])
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == StringEndsWith(a[j], suffix[j])
  {
    result := result + [StringEndsWith(a[i], suffix[i])];
    i := i + 1;
  }
}
// </vc-code>
