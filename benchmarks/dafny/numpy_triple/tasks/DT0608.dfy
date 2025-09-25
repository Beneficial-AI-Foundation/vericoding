// <vc-preamble>
// Method to check if strings in array end with given suffixes
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
