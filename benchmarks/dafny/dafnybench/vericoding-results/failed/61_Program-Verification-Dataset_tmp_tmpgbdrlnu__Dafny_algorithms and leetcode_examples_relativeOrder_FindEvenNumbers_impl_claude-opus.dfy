predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
lemma EvenNumbersSubset(arr: array<int>, evenNumbers: array<int>, i: int, j: int)
  requires 0 <= i <= arr.Length
  requires 0 <= j <= evenNumbers.Length
  requires forall k :: 0 <= k < j ==> exists m :: 0 <= m < i && evenNumbers[k] == arr[m] && IsEven(arr[m])
  ensures forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..i]
  ensures forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..]
{
}

function CountEvens(arr: array<int>, i: int): int
  requires 0 <= i <= arr.Length
  reads arr
{
  if i == 0 then 0
  else if IsEven(arr[i-1]) then CountEvens(arr, i-1) + 1
  else CountEvens(arr, i-1)
}

lemma CountEvensMonotonic(arr: array<int>, i: int, j: int)
  requires 0 <= i <= j <= arr.Length
  ensures CountEvens(arr, i) <= CountEvens(arr, j)
{
  if i == j {
    // Base case: trivial
  } else {
    CountEvensMonotonic(arr, i, j-1);
    // CountEvens(arr, i) <= CountEvens(arr, j-1) <= CountEvens(arr, j)
  }
}

lemma CountEvensStrictlyIncreases(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  requires IsEven(arr[i])
  ensures CountEvens(arr, i+1) == CountEvens(arr, i) + 1
{
  // By definition of CountEvens
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
  var i := 0;
  
  // First pass: count even numbers
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count >= 0
    invariant count == CountEvens(arr, i)
  {
    if IsEven(arr[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  evenNumbers := new int[count];
  
  if count == 0 {
    return;
  }
  
  // Second pass: copy even numbers
  i := 0;
  var j := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= j <= count
    invariant j <= evenNumbers.Length
    invariant evenNumbers.Length == count
    invariant j == CountEvens(arr, i)
    invariant forall k :: 0 <= k < j ==> IsEven(evenNumbers[k])
    invariant forall k :: 0 <= k < j ==> exists m :: 0 <= m < i && evenNumbers[k] == arr[m]
    invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> exists m :: 0 <= m < j && evenNumbers[m] == arr[k]
    invariant forall k, l :: 0 <= k < l < j ==>
      exists n, m :: 0 <= n < m < i && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
  {
    if IsEven(arr[i]) {
      CountEvensStrictlyIncreases(arr, i);
      assert CountEvens(arr, i+1) == CountEvens(arr, i) + 1;
      CountEvensMonotonic(arr, i+1, arr.Length);
      assert count == CountEvens(arr, arr.Length) >= CountEvens(arr, i+1) == j + 1;
      assert j < count;
      evenNumbers[j] := arr[i];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

