/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma lemma_append_seq<T>(s1: seq<T>, s2: seq<T>)
  ensures forall x :: 0 <= x < |s1| ==> (s1 + s2)[x] == s1[x]
  ensures forall x :: |s1| <= x < |s1| + |s2| ==> (s1 + s2)[x] == s2[x - |s1|]
{}
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
  var result: seq<int> := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < |result| ==> IsOdd(result[k])
    invariant forall k :: 0 <= k < |result| ==> result[k] in arr[..]
    invariant forall k :: 0 <= k < i && IsOdd(arr[k]) ==> arr[k] in result
  {
    if IsOdd(arr[i]) {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
  oddList := result;
}
// </vc-code>

