method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < key
  ensures forall i :: n <= i < a.Length ==> a[i] >= key
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < a.Length ==> a[i] >= key
  {
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  n := lo;
}

method Tangent(r: array<int>, x: array<int>)
  returns (found: bool)
  requires forall i:: 1 <= i < x.Length ==> 
           x[i-1] < x[i]
  requires forall i, j ::
           0 <= i < j < x.Length ==>
           x[i] < x[j]
  ensures !found ==>
          forall i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length ==>
          r[i] != x[j]
  ensures found ==>
          exists i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length &&
          r[i] == x[j]
{
  found := false;
  var i := 0;
  
  while i < r.Length && !found
    invariant 0 <= i <= r.Length
    invariant !found ==> forall k, j :: 0 <= k < i && 0 <= j < x.Length ==> r[k] != x[j]
    invariant found ==> exists k, j :: 0 <= k < r.Length && 0 <= j < x.Length && r[k] == x[j]
  {
    var n := BinarySearch(x, r[i]);
    
    if n < x.Length && x[n] == r[i] {
      found := true;
    }
    
    i := i + 1;
  }
}