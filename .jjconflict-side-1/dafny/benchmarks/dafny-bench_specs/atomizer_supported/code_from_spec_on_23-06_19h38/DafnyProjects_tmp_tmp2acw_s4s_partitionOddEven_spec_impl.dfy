// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
//IMPL partitionOddEven
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])  
{
  var left := 0;
  var right := a.Length - 1;
  
  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < left ==> odd(a[k])
    invariant forall k :: right < k < a.Length ==> even(a[k])
  {
    if odd(a[left]) {
      left := left + 1;
    } else if even(a[right]) {
      right := right - 1;
    } else {
      // a[left] is even and a[right] is odd, so swap them
      a[left], a[right] := a[right], a[left];
      left := left + 1;
      right := right - 1;
    }
  }
}

//ATOM 
predicate  odd(n: nat) { n % 2 == 1 }

//ATOM 
predicate  even(n: nat) { n % 2 == 0 }

//IMPL testPartitionOddEven
method testPartitionOddEven() {
  var a := new nat[5];
  a[0], a[1], a[2], a[3], a[4] := 2, 3, 4, 5, 6;
  partitionOddEven(a);
}