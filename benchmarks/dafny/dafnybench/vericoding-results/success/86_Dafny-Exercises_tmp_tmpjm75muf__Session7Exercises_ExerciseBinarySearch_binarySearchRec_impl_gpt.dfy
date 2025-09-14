predicate sorted(s : seq<int>) {
    forall u, w :: 0 <= u < w < |s| ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
lemma prefix_le_from_point(s: seq<int>, m: int, x: int)
  requires sorted(s)
  requires 0 <= m < |s|
  requires s[m] <= x
  ensures forall k :: 0 <= k <= m ==> s[k] <= x
{
  forall k | 0 <= k <= m
    ensures s[k] <= x
  {
    if k < m {
      assert 0 <= k < m < |s|;
      assert s[k] <= s[m];
      assert s[m] <= x;
    } else {
      assert k == m;
      assert s[k] == s[m];
      assert s[m] <= x;
      assert s[k] <= x;
    }
  }
}

lemma suffix_gt_from_point(s: seq<int>, m: int, x: int)
  requires sorted(s)
  requires 0 <= m < |s|
  requires s[m] > x
  ensures forall k :: m <= k < |s| ==> s[k] > x
{
  forall k | m <= k < |s|
    ensures s[k] > x
  {
    if k == m {
      assert s[k] == s[m];
      assert s[k] > x;
    } else {
      assert m < k < |s|;
      assert x < s[m];
      assert s[m] <= s[k];
      assert x < s[k];
    }
  }
}

lemma prefix_le_from_point_arr(v: array<int>, m: int, x: int)
  requires sorted(v[0..v.Length])
  requires 0 <= m < v.Length
  requires v[m] <= x
  ensures forall k :: 0 <= k <= m ==> v[k] <= x
{
  var s := v[0..v.Length];
  prefix_le_from_point(s, m, x);
  forall k | 0 <= k <= m
    ensures v[k] <= x
  {
    assert |s| == v.Length;
    assert 0 <= k <= m;
    assert m < |s|;
    assert k < |s|;
    assert s[k] <= x;
    assert s[k] == v[k];
  }
}

lemma suffix_gt_from_point_arr(v: array<int>, m: int, x: int)
  requires sorted(v[0..v.Length])
  requires 0 <= m < v.Length
  requires v[m] > x
  ensures forall k :: m <= k < v.Length ==> v[k] > x
{
  var s := v[0..v.Length];
  suffix_gt_from_point(s, m, x);
  forall k | m <= k < v.Length
    ensures v[k] > x
  {
    assert |s| == v.Length;
    assert m <= k < |s|;
    assert s[k] > x;
    assert s[k] == v[k];
  }
}
// </vc-helpers>

// <vc-spec>
method binarySearchRec(v:array<int>, elem:int, c:int, f:int) returns (p:int)
 requires sorted(v[0..v.Length])
 requires 0<=c<=f+1<=v.Length//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
 requires forall k::0<=k<c ==> v[k]<=elem
 requires forall k::f<k<v.Length ==> v[k]>elem
 decreases f-c
 ensures -1<=p<v.Length
 ensures (forall u::0<=u<=p ==> v[u]<=elem) && (forall w::p<w<v.Length ==> v[w]>elem)
// </vc-spec>
// <vc-code>
{
  if c == f + 1 {
    p := f;
  } else {
    assert c <= f;
    var m := c + (f - c) / 2;
    assert 0 <= f - c;
    assert c <= m;
    assert m <= f;
    assert 0 <= m < v.Length;

    if v[m] <= elem {
      prefix_le_from_point_arr(v, m, elem);
      assert f - (m + 1) < f - c;
      p := binarySearchRec(v, elem, m + 1, f);
    } else {
      suffix_gt_from_point_arr(v, m, elem);
      assert (m - 1) - c < f - c;
      p := binarySearchRec(v, elem, c, m - 1);
    }
  }
}
// </vc-code>

