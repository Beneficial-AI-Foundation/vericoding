//ATOM
 
predicate odd(n: nat) { n % 2 == 1 }


//ATOM
predicate even(n: nat) { n % 2 == 0 }


//IMPL
// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
method partitionOddEven(a: array<nat>) 
 modifies a
 ensures multiset(a[..]) == multiset(old(a[..]))
 ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]) 
{
    if a.Length <= 1 {
        return;
    }
    
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
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