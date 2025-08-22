//IMPL 
method Tangent(r: array<int>, x: array<int>) returns (b: bool)
  requires forall i, j :: 0 <= i <= j < x.Length ==> x[i] <= x[j] // values in x will be in ascending order or empty
  requires forall i, j :: (0 <= i < r.Length && 0 <= j < x.Length) ==> (r[i] >= 0 && x[j] >= 0)    // x and r will contain no negative values
  ensures !b ==> forall i, j :: 0 <= i< r.Length && 0 <= j < x.Length ==> r[i] != x[j]  
  ensures b ==> exists i, j :: 0 <= i< r.Length && 0 <= j < x.Length && r[i] == x[j]
{
  b := false;
  
  var i := 0;
  while i < r.Length
    invariant 0 <= i <= r.Length
    invariant !b ==> forall ii, j :: 0 <= ii < i && 0 <= j < x.Length ==> r[ii] != x[j]
    invariant b ==> exists ii, j :: 0 <= ii < r.Length && 0 <= j < x.Length && r[ii] == x[j]
  {
    var j := 0;
    while j < x.Length
      invariant 0 <= j <= x.Length
      invariant !b ==> forall jj :: 0 <= jj < j ==> r[i] != x[jj]
      invariant !b ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < x.Length ==> r[ii] != x[jj]
      invariant b ==> exists ii, jj :: 0 <= ii < r.Length && 0 <= jj < x.Length && r[ii] == x[jj]
    {
      if r[i] == x[j] {
        b := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}