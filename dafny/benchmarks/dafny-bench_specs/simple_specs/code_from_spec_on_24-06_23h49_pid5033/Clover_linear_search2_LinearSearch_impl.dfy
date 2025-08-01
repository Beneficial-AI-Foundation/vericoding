//IMPL 
method LinearSearch(a: array<int>, e: int) returns (n:int)
 requires exists i::0<=i<a.Length && a[i]==e
 ensures 0<=n<a.Length && a[n]==e
 ensures forall k :: 0 <= k < n ==> a[k]!=e
{
    n := 0;
    while n < a.Length && a[n] != e
        invariant 0 <= n <= a.Length
        invariant forall k :: 0 <= k < n ==> a[k] != e
        decreases a.Length - n
    {
        n := n + 1;
    }
}