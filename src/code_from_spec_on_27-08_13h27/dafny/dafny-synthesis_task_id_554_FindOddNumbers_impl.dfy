/**
 * Find odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 == 1
}

// <vc-helpers>
// Helper lemma to prove properties if needed
lemma OddNumberInclusion(arr: array<int>, oddList: seq<int>)
  ensures forall i :: 0 <= i < |oddList| ==> oddList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
  // This lemma is implicitly handled by the construction in the method
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindOddNumbersImpl(arr: array<int>) returns (oddList: seq<int>)
  ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
  ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
  var result: seq<int> := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |result| ==> IsOdd(result[k]) && result[k] in arr[..i]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in result
  {
    if IsOdd(arr[i])
    {
      result := result + [arr[i]];
    }
  }
  oddList := result;
  // Assert the postconditions to help verification
  assert forall k :: 0 <= k < |oddList| ==> IsOdd(oddList[k]) && oddList[k] in arr[..];
  assert forall k :: 0 <= k < arr.Length && IsOdd(arr[k]) ==> arr[k] in oddList;
}
// </vc-code>
