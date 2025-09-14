/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
// No helper code required for this verification.
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
  var res: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |res| ==> IsNegative(res[k]) && res[k] in arr[..]
    invariant forall j :: 0 <= j < i && IsNegative(arr[j]) ==> arr[j] in res
    decreases arr.Length - i
  {
    if IsNegative(arr[i]) {
      res := res + [arr[i]];
    }
    i := i + 1;
  }
  negativeList := res;
  return;
}
// </vc-code>

