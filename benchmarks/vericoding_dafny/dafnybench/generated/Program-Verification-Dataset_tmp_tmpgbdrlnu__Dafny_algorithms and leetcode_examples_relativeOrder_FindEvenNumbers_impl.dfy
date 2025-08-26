predicate IsEven (n: int)
{
  n % 2 == 0
}

// <vc-helpers>
function CountEvenNumbers(arr: array<int>, start: int, end: int): int
  requires 0 <= start <= end <= arr.Length
  reads arr
  decreases end - start
{
  if start == end then 0
  else (if IsEven(arr[start]) then 1 else 0) + CountEvenNumbers(arr, start + 1, end)
}

lemma CountEvenNumbersProperty(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  ensures CountEvenNumbers(arr, 0, i + 1) == CountEvenNumbers(arr, 0, i) + (if IsEven(arr[i]) then 1 else 0)
{
  // The proof follows by unfolding the definition of CountEvenNumbers
  if i == 0 {
    // Base case: CountEvenNumbers(arr, 0, 1) == CountEvenNumbers(arr, 0, 0) + (if IsEven(arr[0]) then 1 else 0)
    assert CountEvenNumbers(arr, 0, 0) == 0;
    assert CountEvenNumbers(arr, 0, 1) == (if IsEven(arr[0]) then 1 else 0) + CountEvenNumbers(arr, 1, 1);
    assert CountEvenNumbers(arr, 1, 1) == 0;
  } else {
    // Inductive case: use the recursive structure
    assert CountEvenNumbers(arr, 0, i + 1) == (if IsEven(arr[0]) then 1 else 0) + CountEvenNumbers(arr, 1, i + 1);
    assert CountEvenNumbers(arr, 0, i) == (if IsEven(arr[0]) then 1 else 0) + CountEvenNumbers(arr, 1, i);
    // Use the property recursively on the suffix
    CountEvenNumbersSuffixProperty(arr, 1, i);
  }
}

lemma CountEvenNumbersSuffixProperty(arr: array<int>, start: int, i: int)
  requires 0 <= start <= i < arr.Length
  ensures CountEvenNumbers(arr, start, i + 1) == CountEvenNumbers(arr, start, i) + (if IsEven(arr[i]) then 1 else 0)
{
  if start == i {
    assert CountEvenNumbers(arr, start, i) == 0;
    assert CountEvenNumbers(arr, start, i + 1) == (if IsEven(arr[i]) then 1 else 0);
  } else {
    assert CountEvenNumbers(arr, start, i + 1) == (if IsEven(arr[start]) then 1 else 0) + CountEvenNumbers(arr, start + 1, i + 1);
    assert CountEvenNumbers(arr, start, i) == (if IsEven(arr[start]) then 1 else 0) + CountEvenNumbers(arr, start + 1, i);
    CountEvenNumbersSuffixProperty(arr, start + 1, i);
  }
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers (arr: array<int>)
  returns (evenNumbers: array<int>)
  ensures forall x :: x in arr[..] && IsEven(x) ==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
    ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
    exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  // Count even numbers
  var count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == CountEvenNumbers(arr, 0, i)
  {
    CountEvenNumbersProperty(arr, i);
    if IsEven(arr[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  // Create result array
  evenNumbers := new int[count];
  
  // Fill result array
  var j := 0;
  i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= j <= count
    invariant j <= evenNumbers.Length
    invariant j == CountEvenNumbers(arr, 0, i)
    invariant forall k :: 0 <= k < j ==> IsEven(evenNumbers[k])
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..]
    invariant forall k1, k2 :: 0 <= k1 < k2 < j ==> 
      exists n1, n2 :: 0 <= n1 < n2 < i && evenNumbers[k1] == arr[n1] && evenNumbers[k2] == arr[n2]
    invariant forall x :: x in arr[0..i] && IsEven(x) ==> x in evenNumbers[0..j]
  {
    CountEvenNumbersProperty(arr, i);
    if IsEven(arr[i]) {
      evenNumbers[j] := arr[i];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>