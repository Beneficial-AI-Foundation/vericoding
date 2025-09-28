// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma StrictPrefixLess(xs: array<int>, mid: int, t: int)
  requires 0 <= mid < xs.Length
  requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
  requires xs[mid] < t
  ensures forall i :: 0 <= i <= mid ==> xs[i] < t
{
  forall i | 0 <= i <= mid
    ensures xs[i] < t
  {
    if i == mid {
      assert xs[i] == xs[mid];
      assert xs[i] < t;
    } else {
      assert i < mid;
      assert 0 <= i < mid < xs.Length;
      assert xs[i] < xs[mid];
      assert xs[mid] < t;
      assert xs[i] < t;
    }
  }
}

lemma StrictSuffixGe(xs: array<int>, mid: int, t: int)
  requires 0 <= mid < xs.Length
  requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
  requires t <= xs[mid]
  ensures forall j :: mid <= j < xs.Length ==> t <= xs[j]
{
  forall j | mid <= j < xs.Length
    ensures t <= xs[j]
  {
    if j == mid {
      assert t <= xs[j];
    } else {
      assert mid < j;
      assert 0 <= mid < j < xs.Length;
      assert xs[mid] < xs[j];
      assert xs[mid] <= xs[j];
      assert t <= xs[mid];
      assert t <= xs[j];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SearchInsert(xs: array<int>, target: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < xs.Length ==> xs[i] < xs[j]
    ensures 0 <= result <= xs.Length
    ensures forall i :: 0 <= i < result ==> xs[i] < target
    ensures result < xs.Length ==> target <= xs[result]
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := xs.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= xs.Length
    invariant forall i :: 0 <= i < lo ==> xs[i] < target
    invariant forall i :: hi <= i < xs.Length ==> target <= xs[i]
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid < hi;
    assert 0 <= mid < xs.Length;
    if xs[mid] < target {
      StrictPrefixLess(xs, mid, target);
      lo := mid + 1;
    } else {
      StrictSuffixGe(xs, mid, target);
      hi := mid;
    }
  }
  result := lo;
}
// </vc-code>
