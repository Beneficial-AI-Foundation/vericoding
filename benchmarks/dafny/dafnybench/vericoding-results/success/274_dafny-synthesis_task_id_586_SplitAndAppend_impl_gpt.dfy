

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SplitAndAppend(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0 && n < |l|
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i + n) % |l|]
// </vc-spec>
// <vc-code>
{
  var left := l[n..];
  var right := l[..n];
  r := left + right;

  // Help the prover with lengths
  assert |left| == |l| - n;
  assert |right| == n;
  assert |r| == |left| + |right|;
  assert |r| == |l|;
  assert |l| > 0;

  // Prove element-wise correspondence
  forall i | 0 <= i < |l|
    ensures r[i] == l[(i + n) % |l|]
  {
    if i < |left| {
      // r[i] comes from left part
      assert i < |left|;
      assert r[i] == (left + right)[i];
      assert (left + right)[i] == left[i];
      assert left[i] == l[n + i];
      assert i + n < |l|;
      assert (i + n) % |l| == i + n;
    } else {
      // r[i] comes from right part
      var j := i - |left|;
      assert |left| == |l| - n;
      assert 0 <= j;
      assert j < |right|; // since i < |l| = |left| + |right|
      assert r[i] == (left + right)[i];
      assert (left + right)[i] == right[j];
      assert right[j] == l[j];
      assert j == i - (|l| - n);
      assert i + n >= |l|;
      assert i + n < 2 * |l|;
      assert (i + n) % |l| == i + n - |l|;
    }
  }
}
// </vc-code>

