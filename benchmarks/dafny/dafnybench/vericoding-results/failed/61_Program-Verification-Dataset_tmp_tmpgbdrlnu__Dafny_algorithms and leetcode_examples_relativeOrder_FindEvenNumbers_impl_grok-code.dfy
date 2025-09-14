predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..];
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
var len := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant len == |{j | 0 <= j < i && IsEven(arr[j])}|
  {
    if IsEven(arr[i]) {
      len := len + 1;
    }
    i := i + 1;
  }
  evenNumbers := new int[len];
  var originalIndices := new int[len];
  var idx := 0;
  i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= idx <= len
    invariant idx == |{j | 0 <= j < i && IsEven(arr[j])}|
    invariant forall p :: 0 <= p < idx ==> 0 <= originalIndices[p] < i && arr[originalIndices[p]] == evenNumbers[p] && IsEven(arr[originalIndices[p]])
    invariant forall p, q :: 0 <= p < q < idx ==> originalIndices[p] < originalIndices[q]
    invariant forall x :: x in arr[..i] && IsEven(x) ==> x in evenNumbers[..idx]
  {
    if IsEven(arr[i]) {
      evenNumbers[idx] := arr[i];
      originalIndices[idx] := i;
      idx := idx + 1;
    }
    i := i + 1;
  }
// </vc-code>

