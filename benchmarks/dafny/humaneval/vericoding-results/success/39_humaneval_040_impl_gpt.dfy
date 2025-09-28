// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>
predicate HasTripleUpToK(l: seq<int>, k: int)
  requires 0 <= k <= |l|
{
  exists i, j, kk :: 0 <= i < j < kk < k && l[i] + l[j] + l[kk] == 0
}

predicate HasTripleAtK(l: seq<int>, k: int)
  requires 0 <= k < |l|
{
  exists i, j :: 0 <= i < j < k && l[i] + l[j] + l[k] == 0
}

lemma StepLemma(l: seq<int>, k: int)
  requires 0 <= k < |l|
  ensures HasTripleUpToK(l, k+1) == (HasTripleUpToK(l, k) || HasTripleAtK(l, k))
{
  // (=>) direction
  if HasTripleUpToK(l, k+1) {
    var i, j, kk :| 0 <= i < j < kk < k + 1 && l[i] + l[j] + l[kk] == 0;
    if kk < k {
      assert 0 <= i < j < kk < k && l[i] + l[j] + l[kk] == 0;
      assert exists ii, jj, kk2 :: ii == i && jj == j && kk2 == kk && 0 <= ii < jj < kk2 < k && l[ii] + l[jj] + l[kk2] == 0;
      assert HasTripleUpToK(l, k);
    } else {
      assert kk == k;
      assert 0 <= i < j < k && l[i] + l[j] + l[k] == 0;
      assert exists ii, jj :: ii == i && jj == j && 0 <= ii < jj < k && l[ii] + l[jj] + l[k] == 0;
      assert HasTripleAtK(l, k);
    }
    assert HasTripleUpToK(l, k) || HasTripleAtK(l, k);
  }

  // (<=) direction
  if HasTripleUpToK(l, k) || HasTripleAtK(l, k) {
    if HasTripleUpToK(l, k) {
      var i2, j2, kk2 :| 0 <= i2 < j2 < kk2 < k && l[i2] + l[j2] + l[kk2] == 0;
      assert 0 <= i2 < j2 < kk2 < k + 1 && l[i2] + l[j2] + l[kk2] == 0;
      assert exists ii, jj, kk3 :: ii == i2 && jj == j2 && kk3 == kk2 && 0 <= ii < jj < kk3 < k + 1 && l[ii] + l[jj] + l[kk3] == 0;
      assert HasTripleUpToK(l, k+1);
    } else {
      var i3, j3 :| 0 <= i3 < j3 < k && l[i3] + l[j3] + l[k] == 0;
      assert 0 <= i3 < j3 < k + 1;
      assert exists ii, jj, kk3 :: ii == i3 && jj == j3 && kk3 == k && 0 <= ii < jj < kk3 < k + 1 && l[ii] + l[jj] + l[kk3] == 0;
      assert HasTripleUpToK(l, k+1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var k := 0;
  var res := false;
  while k < n
    invariant 0 <= k <= n
    invariant res == HasTripleUpToK(l, k)
    decreases n - k
  {
    var found := false;
    var j := 0;
    while j < k
      invariant 0 <= j <= k
      invariant found == (exists jj :: 0 <= jj < j && (exists ii :: 0 <= ii < jj && l[ii] + l[jj] + l[k] == 0))
      decreases k - j
    {
      var cur := false;
      var i := 0;
      while i < j
        invariant 0 <= i <= j
        invariant cur == (exists ii :: 0 <= ii < i && l[ii] + l[j] + l[k] == 0)
        decreases j - i
      {
        if l[i] + l[j] + l[k] == 0 {
          cur := true;
        }
        i := i + 1;
      }
      found := found || cur;
      j := j + 1;
    }
    assert 0 <= k < n;
    assert found == HasTripleAtK(l, k);
    res := res || found;
    StepLemma(l, k);
    assert res == (HasTripleUpToK(l, k) || HasTripleAtK(l, k));
    assert HasTripleUpToK(l, k+1) == (HasTripleUpToK(l, k) || HasTripleAtK(l, k));
    k := k + 1;
  }
  result := res;
}
// </vc-code>
