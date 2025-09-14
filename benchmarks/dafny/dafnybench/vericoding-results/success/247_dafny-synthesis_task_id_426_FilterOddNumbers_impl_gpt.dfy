/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>

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
    invariant forall j :: 0 <= j < |res| ==> IsOdd(res[j]) && res[j] in arr[..i]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in res
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

