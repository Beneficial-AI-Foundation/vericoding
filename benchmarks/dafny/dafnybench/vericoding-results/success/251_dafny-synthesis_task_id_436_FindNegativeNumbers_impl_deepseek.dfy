/**
 * Find negative numbers from an array of numbers
 **/

predicate IsNegative(n: int)
{
    n < 0
}

// <vc-helpers>
lemma negative_in_arr(a: array<int>, s: seq<int>, n: int)
  requires n in s
  requires forall x :: x in s ==> x in a[..]
  ensures n in a[..]
{
}

lemma seq_in_array(a: array<int>, s: seq<int>, n: int)
  requires n in a[..]
  requires forall x :: x in s ==> x in a[..]
  ensures n in s || (forall x :: x in s ==> x != n)
{
}

lemma no_duplicates_preserved(s: seq<int>, x: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  requires x !in s
  ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
}
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
  negativeList := [];
  var index := 0;
  
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall x :: x in negativeList ==> IsNegative(x) && x in arr[..]
    invariant forall i :: 0 <= i < arr.Length && i < index && IsNegative(arr[i]) ==> arr[i] in negativeList
    invariant forall i, j :: 0 <= i < j < |negativeList| ==> negativeList[i] != negativeList[j]
  {
    if IsNegative(arr[index]) {
      if arr[index] !in negativeList {
        negativeList := negativeList + [arr[index]];
      }
    }
    index := index + 1;
  }
}
// </vc-code>

