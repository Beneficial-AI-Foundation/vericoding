method FindEvenNumbers (arr: array<int>) returns (evenNumbers: array<int>)
  ensures forall x {:trigger (x%2) }:: x in arr[..] &&  (x%2==0)==> x in evenNumbers[..]
  ensures forall x :: x !in arr[..] ==> x !in evenNumbers[..]
  ensures forall k :: 0 <= k < evenNumbers.Length ==> evenNumbers[k] % 2 == 0
  ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
                           exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
  // First, count the number of even elements
  var count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == |set j | 0 <= j < i && arr[j] % 2 == 0|
  {
    if arr[i] % 2 == 0 {
      count := count + 1;
      // Help prove the invariant by showing the set grows by exactly 1
      assert arr[i] % 2 == 0;
      assert i !in set j | 0 <= j < i && arr[j] % 2 == 0;
      assert (set j | 0 <= j < i+1 && arr[j] % 2 == 0) == 
             (set j | 0 <= j < i && arr[j] % 2 == 0) + {i};
    } else {
      assert arr[i] % 2 != 0;
      assert (set j | 0 <= j < i+1 && arr[j] % 2 == 0) == 
             (set j | 0 <= j < i && arr[j] % 2 == 0);
    }
    i := i + 1;
  }
  
  // Create the result array
  evenNumbers := new int[count];
  
  // Fill the result array with even numbers
  var j := 0;
  i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant 0 <= j <= count
    invariant j == |set k | 0 <= k < i && arr[k] % 2 == 0|
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] % 2 == 0
    invariant forall k :: 0 <= k < j ==> evenNumbers[k] in arr[..]
    invariant forall x :: x in arr[0..i] && x % 2 == 0 ==> x in evenNumbers[0..j]
    invariant forall k, l :: 0 <= k < l < j ==>
               exists n, m :: 0 <= n < m < i && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]
    invariant count == |set k | 0 <= k < arr.Length && arr[k] % 2 == 0|
    invariant forall k :: 0 <= k < j ==> exists n :: 0 <= n < i && evenNumbers[k] == arr[n]
  {
    if arr[i] % 2 == 0 {
      assert j < count; // This ensures j is within bounds
      evenNumbers[j] := arr[i];
      // Prove that all invariants are maintained
      assert evenNumbers[j] % 2 == 0;
      assert evenNumbers[j] in arr[..];
      assert evenNumbers[j] == arr[i];
      
      // Help prove that the new element is now in evenNumbers[0..j+1]
      assert arr[i] in evenNumbers[0..j+1];
      
      // Before incrementing j, help prove the set cardinality assertion
      assert i in set k | 0 <= k < i+1 && arr[k] % 2 == 0;
      assert i !in set k | 0 <= k < i && arr[k] % 2 == 0;
      SetCardinalityLemma(arr, i);
      
      j := j + 1;
    } else {
      // Prove that no new even element is added when arr[i] is odd
      assert arr[i] % 2 != 0;
      assert i !in set k | 0 <= k < i+1 && arr[k] % 2 == 0;
      SetCardinalityLemmaOdd(arr, i);
    }
    i := i + 1;
  }
  
  // Prove postconditions
  assert i == arr.Length;
  assert j == count;
  assert count == |set k | 0 <= k < arr.Length && arr[k] % 2 == 0|;
  assert j == evenNumbers.Length;
  
  // Prove first postcondition
  forall x | x in arr[..] && x % 2 == 0
    ensures x in evenNumbers[..]
  {
    assert x in arr[0..arr.Length];
    assert x in evenNumbers[0..j];
    assert evenNumbers[0..j] == evenNumbers[..];
  }
  
  // Prove second postcondition
  forall x | x !in arr[..]
    ensures x !in evenNumbers[..]
  {
    if x in evenNumbers[..] {
      assert exists k :: 0 <= k < evenNumbers.Length && evenNumbers[k] == x;
      var k :| 0 <= k < evenNumbers.Length && evenNumbers[k] == x;
      assert evenNumbers[k] in arr[..];
      assert x in arr[..];
      assert false;
    }
  }
}
// </vc-code>
// <vc-helpers>
lemma SetCardinalityLemma(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  requires arr[i] % 2 == 0
  ensures |set k | 0 <= k < i+1 && arr[k] % 2 == 0| == |set k | 0 <= k < i && arr[k] % 2 == 0| + 1
{
  var s1 := set k | 0 <= k < i && arr[k] % 2 == 0;
  var s2 := set k | 0 <= k < i+1 && arr[k] % 2 == 0;
  
  assert i !in s1;
  assert arr[i] % 2 == 0;
  assert s2 == s1 + {i};
}

lemma SetCardinalityLemmaOdd(arr: array<int>, i: int)
  requires 0 <= i < arr.Length
  requires arr[i] % 2 != 0
  ensures |set k | 0 <= k < i+1 && arr[k] % 2 == 0| == |set k | 0 <= k < i && arr[k] % 2 == 0|
{
  var s1 := set k | 0 <= k < i && arr[k] % 2 == 0;
  var s2 := set k | 0 <= k < i+1 && arr[k] % 2 == 0;
  
  assert arr[i] % 2 != 0;
  assert i !in s2;
  assert s2 == s1;
}
// </vc-helpers>