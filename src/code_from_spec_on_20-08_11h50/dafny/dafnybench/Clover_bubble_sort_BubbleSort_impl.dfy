// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x, y :: 0 <= x < i && i <= y < n ==> a[x] <= a[y]
  {
    var j := n - 1;
    
    while j > i
      invariant i < j <= n - 1
      invariant multiset(a[..]) == multiset(old(a[..]))
      invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
      invariant forall x, y :: 0 <= x < i && i <= y < n ==> a[x] <= a[y]
      invariant forall k :: i < k <= j ==> a[i] <= a[k]
    {
      if a[j-1] > a[j] {
        // Swap elements
        var temp := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>