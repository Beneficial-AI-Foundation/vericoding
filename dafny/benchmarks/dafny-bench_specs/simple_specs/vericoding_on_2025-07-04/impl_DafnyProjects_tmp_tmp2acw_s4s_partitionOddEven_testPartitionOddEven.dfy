//ATOM

predicate odd(n: nat) { n % 2 == 1 }

//ATOM

predicate even(n: nat) { n % 2 == 0 }

//ATOM

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
method partitionOddEven(a: array<nat>) 
 modifies a
 ensures multiset(a[..]) == multiset(old(a[..]))
 ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]) 
{
  assume multiset(a[..]) == multiset(old(a[..]));
  assume ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
}

//IMPL testPartitionOddEven

/* code modified by LLM (iteration 1): Added proper implementation for test method */
method testPartitionOddEven() {
  // Test with empty array
  var a1 := new nat[0];
  partitionOddEven(a1);
  
  // Test with single element
  var a2 := new nat[1];
  a2[0] := 3;
  partitionOddEven(a2);
  
  // Test with mixed odd/even elements
  var a3 := new nat[4];
  a3[0] := 2; a3[1] := 3; a3[2] := 4; a3[3] := 5;
  partitionOddEven(a3);
}