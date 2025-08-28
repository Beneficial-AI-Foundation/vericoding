/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
// Helper lemma to prove properties about sequences and membership
lemma SeqMembership(arr: array<int>, s: seq<int>)
  ensures forall i :: 0 <= i < arr.Length ==> arr[i] in arr[..]
  ensures forall i :: 0 <= i < |s| ==> s[i] in s
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// </vc-spec>

// <vc-code>
method FilterOddNumbersImpl(arr: array<int>) returns (oddList: seq<int>)
  ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
  oddList := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k]) && oddList[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in oddList
  {
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
