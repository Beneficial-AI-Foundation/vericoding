

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
// </vc-spec>
// <vc-code>
{
  var bi := 0;
  var bj := 0;
  var best: nat := if a[0] < b[0] then b[0] - a[0] else a[0] - b[0];

  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= bi < a.Length
    invariant 0 <= bj < b.Length
    invariant best == (if a[bi] < b[bj] then b[bj] - a[bi] else a[bi] - b[bj])
    invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> best <= (if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj])
  {
    var j := 0;
    while j < b.Length
      invariant 0 <= j <= b.Length
      invariant 0 <= bi < a.Length
      invariant 0 <= bj < b.Length
      invariant best == (if a[bi] < b[bj] then b[bj] - a[bi] else a[bi] - b[bj])
      invariant forall jj :: 0 <= jj < j ==> best <= (if a[i] < b[jj] then b[jj] - a[i] else a[i] - b[jj])
      invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < b.Length ==> best <= (if a[ii] < b[jj] then b[jj] - a[ii] else a[ii] - b[jj])
    {
      var cur: nat := if a[i] < b[j] then b[j] - a[i] else a[i] - b[j];
      if cur < best {
        best := cur;
        bi := i;
        bj := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  d := best;
}
// </vc-code>

