// <vc-preamble>
// Method to check if strings in array end with given suffixes
// </vc-preamble>

// <vc-helpers>
predicate IsSuffix(a: string, s: string) { |s| <= |a| && a[|a|-|s|..] == s }
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
  var n := |a|;
  var arr := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> arr[k] == IsSuffix(a[k], suffix[k])
  {
    var sa := a[i];
    var ss := suffix[i];
    var b := |ss| <= |sa| && sa[|sa|-|ss|..] == ss;
    arr[i] := b;
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>
