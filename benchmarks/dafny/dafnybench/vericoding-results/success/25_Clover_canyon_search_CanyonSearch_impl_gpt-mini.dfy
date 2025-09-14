

// <vc-helpers>
// No helpers needed for this proof.
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
  d := if a[0] < b[0] then b[0] - a[0] else a[0] - b[0];
  var bi := 0;
  var bj := 0;
  var i := 0;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant 0 <= bi < a.Length
    invariant 0 <= bj < b.Length
    invariant d == (if a[bi] < b[bj] then b[bj] - a[bi] else a[bi] - b[bj])
    invariant forall p,q :: 0 <= p < i && 0 <= q < b.Length ==>
                d <= (if a[p] < b[q] then b[q] - a[p] else a[p] - b[q])
  {
    var j := 0;
    while j < b.Length
      decreases b.Length - j
      invariant 0 <= j <= b.Length
      invariant 0 <= bi < a.Length
      invariant 0 <= bj < b.Length
      invariant d == (if a[bi] < b[bj] then b[bj] - a[bi] else a[bi] - b[bj])
      invariant forall q :: 0 <= q < j ==>
                  d <= (if a[i] < b[q] then b[q] - a[i] else a[i] - b[q])
      invariant forall p,q :: 0 <= p < i && 0 <= q < b.Length ==>
                  d <= (if a[p] < b[q] then b[q] - a[p] else a[p] - b[q])
    {
      var diff := if a[i] < b[j] then b[j] - a[i] else a[i] - b[j];
      if diff < d {
        d := diff;
        bi := i;
        bj := j;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

