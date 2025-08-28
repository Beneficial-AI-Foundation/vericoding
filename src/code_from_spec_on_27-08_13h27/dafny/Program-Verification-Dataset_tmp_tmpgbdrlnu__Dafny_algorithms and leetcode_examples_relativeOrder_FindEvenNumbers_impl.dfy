predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
// Helper lemma to ensure ordering in the filtered array
lemma EvenNumbersOrdering(arr: array<int>, evenNumbers: array<int>, evenCount: int)
  requires 0 <= evenCount <= arr.Length
  requires evenNumbers.Length == evenCount
  requires forall i :: 0 <= i < evenCount ==> evenNumbers[i] in arr[..] && IsEven(evenNumbers[i])
  requires forall k, l :: 0 <= k < l < evenCount ==> 
             exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==> 
             exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindEvenNumbersImpl(arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==> 
            exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
  var evenCount := 0;
  for i := 0 to arr.Length
    invariant 0 <= evenCount <= i <= arr.Length
  {
    if IsEven(arr[i]) {
      evenCount := evenCount + 1;
    }
  }

  evenNumbers := new int[evenCount];
  var index := 0;
  var positions: seq<int> := [];
  for i := 0 to arr.Length
    invariant 0 <= index <= i <= arr.Length
    invariant index <= evenCount
    invariant |positions| == index
    invariant forall k :: 0 <= k < index ==> evenNumbers[k] in arr[..] && IsEven(evenNumbers[k])
    invariant forall k :: 0 <= k < index ==> positions[k] < i
    invariant forall k :: 0 <= k < index ==> 0 <= positions[k] < arr.Length && evenNumbers[k] == arr[positions[k]]
    invariant forall k, l :: 0 <= k < l < index ==> positions[k] < positions[l]
  {
    if IsEven(arr[i]) {
      assert index < evenNumbers.Length;
      evenNumbers[index] := arr[i];
      positions := positions + [i];
      index := index + 1;
    }
  }
  
  assert index == evenCount;
  assert forall k, l :: 0 <= k < l < evenNumbers.Length ==> positions[k] < positions[l] && evenNumbers[k] == arr[positions[k]] && evenNumbers[l] == arr[positions[l]];
}
// </vc-code>
