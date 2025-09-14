predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
lemma EvenPreservation(arr: array<int>, i: int, evenNumbers: array<int>, idx: int)
  requires 0 <= i <= arr.Length
  requires 0 <= idx <= i
  requires forall j :: 0 <= j < idx ==> IsEven(evenNumbers[j]) && evenNumbers[j] in arr[0..i]
  ensures forall x :: x in arr[0..i] && IsEven(x) ==> x in evenNumbers[0..idx]
{
}

lemma OrderPreservation(arr: array<int>, evenNumbers: array<int>, idx: int)
  requires 0 <= idx <= evenNumbers.Length
  requires forall j :: 0 <= j < idx ==> evenNumbers[j] in arr[..]
  requires forall j, k :: 0 <= j < k < idx ==> index_of(evenNumbers[j], arr) < index_of(evenNumbers[k], arr)
  ensures forall k, l :: 0 <= k < l < idx ==> exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
{
}

function index_of(x: int, arr: array<int>): int
  requires x in arr[..]
  ensures 0 <= index_of(x, arr) < arr.Length
  ensures arr[index_of(x, arr)] == x
  ensures forall i :: 0 <= i < index_of(x, arr) ==> arr[i] != x
{
  var i: int := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] != x
  {
    if arr[i] == x {
      return i;
    }
    i := i + 1;
  }
  -1
}
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
{
  var count := 0;
  var tempEvenNumbers := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= count <= i
    invariant forall j :: 0 <= j < count ==> IsEven(tempEvenNumbers[j]) && tempEvenNumbers[j] in arr[0..i]
    invariant forall x :: x in arr[0..i] && IsEven(x) ==> x in tempEvenNumbers[0..count]
    invariant forall x :: x !in arr[..] ==> x !in tempEvenNumbers[..]
    invariant forall j, k :: 0 <= j < k < count ==> index_of(tempEvenNumbers[j], arr) < index_of(tempEvenNumbers[k], arr)
  {
    if IsEven(arr[i]) {
      tempEvenNumbers[count] := arr[i];
      count := count + 1;
    }
    i := i + 1;
  }
  evenNumbers := tempEvenNumbers[0..count];
}
// </vc-code>

