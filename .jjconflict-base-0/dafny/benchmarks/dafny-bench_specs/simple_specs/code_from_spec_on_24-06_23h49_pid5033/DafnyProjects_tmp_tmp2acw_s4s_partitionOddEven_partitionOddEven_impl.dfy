//ATOM
 
predicate odd(n: nat) { n % 2 == 1 }


//ATOM
predicate even(n: nat) { n % 2 == 0 }


//IMPL partitionOddEven
method partitionOddEven(a: array<nat>) 
 modifies a
 ensures multiset(a[..]) == multiset(old(a[..]))
 ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j]) 
{
    if a.Length == 0 {
        return;
    }
    
    var left := 0;
    var right := a.Length - 1;
    
    while left < right
        invariant 0 <= left <= a.Length
        invariant -1 <= right < a.Length
        invariant left > right ==> forall i :: 0 <= i <= right ==> odd(a[i])
        invariant left > right ==> forall i :: left <= i < a.Length ==> even(a[i])
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant forall i :: 0 <= i < left ==> odd(a[i])
        invariant forall i :: right < i < a.Length ==> even(a[i])
    {
        if odd(a[left]) {
            left := left + 1;
        } else if even(a[right]) {
            right := right - 1;
        } else {
            // a[left] is even and a[right] is odd, so swap them
            var temp := a[left];
            a[left] := a[right];
            a[right] := temp;
            left := left + 1;
            right := right - 1;
        }
    }
}