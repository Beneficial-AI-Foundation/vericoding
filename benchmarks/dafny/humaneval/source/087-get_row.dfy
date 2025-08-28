type SortSeqState = seq<(int, int)>

method get_row(lst: seq<seq<int>>, x: int) returns (pos: SortSeqState)
  // post-conditions-start
  ensures forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i];
    0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  )
  ensures forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos
  ensures forall i, j :: 0 <= i < j < |pos| ==> less_eq(pos[i], pos[j])
  // post-conditions-end
{
  // impl-start
  pos := [];
  var i := 0;
  while i < |lst|
    // invariants-start
    invariant 0 <= i <= |lst|
    invariant forall j :: 0 <= j < |pos| ==> (
      var (a, b) := pos[j];
      0 <= a < i && 0 <= b < |lst[a]| && lst[a][b] == x
    )
    invariant forall j, k :: 0 <= j < i && 0 <= k < |lst[j]| && lst[j][k] == x ==> (j, k) in pos
    // invariants-end
  {
    var j := 0;
    var pos_i := [];
    ghost var row := lst[i];
    while j < |lst[i]|
      // invariants-start
      invariant 0 <= j <= |lst[i]|
      invariant forall k :: 0 <= k < |pos_i| ==> var (a, b) := pos_i[k];
        a == i && 0 <= b < |row|
      invariant forall k :: 0 <= k < |pos_i| ==> var (a, b) := pos_i[k]; row[b] == x
      invariant forall k :: 0 <= k < j && lst[i][k] == x ==> (i, k) in pos_i
      // invariants-end
    {
      if lst[i][j] == x {
        pos_i := pos_i + [(i, j)];
      }
      j := j + 1;
    }

    pos := pos + pos_i;

    i := i + 1;
  }
  ghost var unsorted := pos;
  pos := SortSeq(pos);
  // assert-start
  assert forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in pos by {
    assert forall i, j :: 0 <= i < |lst| && 0 <= j < |lst[i]| && lst[i][j] == x ==> (i, j) in multiset(pos);
  }
  // assert-end

  // assert-start
  assert forall i :: 0 <= i < |pos| ==> (
    var (a, b) := pos[i]; 0 <= a < |lst| && 0 <= b < |lst[a]| && lst[a][b] == x
  ) by {
    assert forall i :: 0 <= i < |pos| ==> pos[i] in multiset(unsorted);
  }
  // assert-end
  // impl-end
}

function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}

function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}

method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> less_eq(sorted[j], sorted[k])
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> less_eq(sorted[j], sorted[k])
    invariant |sorted| == |s|
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      // invariants-start
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> less_eq(sorted[minIndex], sorted[k])
      // invariants-end
    {
      if less(sorted[j], sorted[minIndex]) {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  // impl-end
}
