// <vc-preamble>
// Method to perform inverse FFT shift on a sequence of real numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define rotateHalf and prove its correctness */
function rotateHalf(x: seq<real>): seq<real>
{
  x[|x| / 2 ..] + x[.. |x| / 2]
}

/* helper modified by LLM (iteration 2): lemma showing rotateHalf matches required indexing */
lemma RotateHalfCorrect(x: seq<real>)
  requires |x| > 0
  ensures forall i :: 0 <= i < |x| ==> rotateHalf(x)[i] == x[(i + |x| / 2) % |x|]
{
  var n := |x|;
  var m := n / 2;
  forall i | 0 <= i < n
    ensures rotateHalf(x)[i] == x[(i + m) % n]
  {
    if i < n - m {
      assert rotateHalf(x) == x[m..] + x[..m];
      assert |x[m..]| == n - m;
      assert (x[m..] + x[..m])[i] == x[m..][i];
      assert x[m..][i] == x[m + i];
      assert 0 <= i + m;
      assert i + m < n;
      assert (i + m) % n == i + m;
    } else {
      var j := i - (n - m);
      assert j >= 0;
      assert j < m;
      assert rotateHalf(x) == x[m..] + x[..m];
      assert |x[m..]| == n - m;
      assert i >= |x[m..]|;
      assert (x[m..] + x[..m])[i] == x[..m][j];
      assert x[..m][j] == x[j];
      assert m < n;
      assert i + m >= n;
      assert 0 <= i + m - n;
      assert i + m - n < n;
      assert (i + m) % n == i + m - n;
      assert x[j] == x[(i + m) % n];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ifftshift(x: seq<real>) returns (result: seq<real>)
  requires |x| > 0
  ensures |result| == |x|
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| / 2) % |x|]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement ifftshift via slices and prove spec in-body */
  var n := |x|;
  var m := n / 2;
  result := x[m..] + x[..m];

  // Prove value relation for all indices
  forall i | 0 <= i < n
    ensures result[i] == x[(i + m) % n]
  {
    if i < n - m {
      assert |x[m..]| == n - m;
      assert result == x[m..] + x[..m];
      assert result[i] == (x[m..] + x[..m])[i];
      assert (x[m..] + x[..m])[i] == x[m..][i];
      assert x[m..][i] == x[m + i];
      assert 0 <= i + m;
      assert i + m < n;
      assert (i + m) % n == i + m;
    } else {
      var j := i - (n - m);
      assert j >= 0;
      assert j < m;
      assert result == x[m..] + x[..m];
      assert |x[m..]| == n - m;
      assert i >= |x[m..]|;
      assert result[i] == (x[m..] + x[..m])[i];
      assert (x[m..] + x[..m])[i] == x[..m][j];
      assert x[..m][j] == x[j];
      assert i + m >= n;
      assert i + m - n == j;
      assert (i + m) % n == i + m - n;
    }
  }
}

// </vc-code>
