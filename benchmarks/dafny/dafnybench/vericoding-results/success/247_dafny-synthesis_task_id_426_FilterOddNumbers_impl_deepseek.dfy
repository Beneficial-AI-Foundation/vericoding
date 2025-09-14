/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

// <vc-helpers>
lemma LemmaOddInSeq(s: seq<int>, n: int)
  requires n in s
  requires IsOdd(n)
  ensures exists i :: 0 <= i < |s| && s[i] == n
{
}

lemma LemmaOddInArray(arr: array<int>, n: int)
  requires n in arr[..]
  requires IsOdd(n)
  ensures exists i :: 0 <= i < arr.Length && arr[i] == n
{
}
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
  oddList := [];
  var index := 0;
  
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    invariant forall j :: 0 <= j < index && IsOdd(arr[j]) ==> arr[j] in oddList
  {
    if IsOdd(arr[index]) {
      oddList := oddList + [arr[index]];
    }
    index := index + 1;
  }
}
// </vc-code>

