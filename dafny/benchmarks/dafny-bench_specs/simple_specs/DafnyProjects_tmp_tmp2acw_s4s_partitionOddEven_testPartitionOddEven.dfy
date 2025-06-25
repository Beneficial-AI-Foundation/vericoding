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
  assume multiset(a[..]) ==> multiset(old(a[..]));
  assume ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]);
}


// SPEC

method testPartitionOddEven() {
}
