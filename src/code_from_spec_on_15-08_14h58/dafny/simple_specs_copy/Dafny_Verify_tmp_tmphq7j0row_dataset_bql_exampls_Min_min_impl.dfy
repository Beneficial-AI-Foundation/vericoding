//IMPL 
method min(a: array<int>, n : int) returns (min : int)
  requires 0 < n <= a.Length
	ensures (exists i : int :: 0 <= i && i < n && a[i] == min)
	ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min)
{
    min := a[0];
    var j := 1;
    
    while j < n
        invariant 1 <= j <= n
        invariant exists i :: 0 <= i < j && a[i] == min
        invariant forall i :: 0 <= i < j ==> a[i] >= min
    {
        if a[j] < min {
            min := a[j];
        }
        j := j + 1;
    }
}