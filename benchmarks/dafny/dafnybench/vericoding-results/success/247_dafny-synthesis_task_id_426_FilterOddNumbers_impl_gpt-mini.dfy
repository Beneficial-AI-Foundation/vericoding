/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
// No helpers required.
// </vc-helpers>

// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |res| ==> IsOdd(res[k]) && res[k] in arr[..]
    invariant forall j :: 0 <= j < i && IsOdd(arr[j]) ==> arr[j] in res
    decreases arr.Length - i
  {
    if IsOdd(arr[i]) {
      res := res + [arr[i]];
    }
    i := i + 1;
  }
  oddList := res;
}
// </vc-code>

