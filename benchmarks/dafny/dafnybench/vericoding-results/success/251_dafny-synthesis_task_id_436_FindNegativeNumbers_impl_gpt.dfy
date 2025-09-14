/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
    // All numbers in the output are negative and exist in the input 
    ensures forall i :: 0 <= i < |negativeList| ==> IsNegative(negativeList[i]) && negativeList[i] in arr[..]
    // All negative numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsNegative(arr[i]) ==> arr[i] in negativeList
// </vc-spec>
// <vc-code>
{
  var s := arr[..];
  var res: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant s == arr[..]
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < |res| ==> IsNegative(res[k]) && res[k] in s
    invariant forall j :: 0 <= j < i && IsNegative(s[j]) ==> s[j] in res
    decreases |s| - i
  {
    if IsNegative(s[i]) {
      assert s[i] in s;
      res := res + [s[i]];
    }
    i := i + 1;
  }
  negativeList := res;
}
// </vc-code>

