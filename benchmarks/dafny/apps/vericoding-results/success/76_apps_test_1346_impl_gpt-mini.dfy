predicate ValidInput(n: int, m: int, p: int, f: seq<int>, g: seq<int>) {
    n >= 1 && m >= 1 &&
    p >= 2 &&
    |f| == n && |g| == m &&
    (forall k :: 0 <= k < |f| ==> f[k] > 0) &&
    (forall k :: 0 <= k < |g| ==> g[k] > 0) &&
    (exists k :: 0 <= k < |f| && f[k] % p != 0) &&
    (exists k :: 0 <= k < |g| && g[k] % p != 0)
}

predicate ValidResult(result: int, n: int, m: int, p: int, f: seq<int>, g: seq<int>) 
    requires p != 0
{
    exists i, j :: 0 <= i < |f| && 0 <= j < |g| &&
            (forall k :: 0 <= k < i ==> f[k] % p == 0) &&
            f[i] % p != 0 &&
            (forall k :: 0 <= k < j ==> g[k] % p == 0) &&
            g[j] % p != 0 &&
            result == i + j &&
            0 <= result < |f| + |g|
}

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, p: int, f: seq<int>, g: seq<int>) returns (result: int)
    requires ValidInput(n, m, p, f, g)
    requires p != 0
    ensures ValidResult(result, n, m, p, f, g)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |f| && f[i] % p == 0
    invariant 0 <= i <= |f|
    invariant forall k :: 0 <= k < i ==> f[k] % p == 0
    decreases |f| - i
  {
    i := i + 1;
  }
  // prove i < |f|
  assert i < |f| by {
    if !(i < |f|) {
      // then i == |f| because i <= |f|
      assert i == |f|;
      // from the loop invariant we get all f[k] divisible by p
      assert (forall k :: 0 <= k < |f| ==> f[k] % p == 0);
      // contradicts ValidInput which guarantees an index with f[k] % p != 0
      assert (exists k :: 0 <= k < |f| && f[k] % p != 0);
      assert false;
    }
  }
  assert f[i] % p != 0;

  var j := 0;
  while j < |g| && g[j] % p == 0
    invariant 0 <= j <= |g|
    invariant forall k :: 0 <= k < j ==> g[k] % p == 0
    decreases |g| - j
  {
    j := j + 1;
  }
  // prove j < |g|
  assert j < |g| by {
    if !(j < |g|) {
      assert j == |g|;
      assert (forall k :: 0 <= k < |g| ==> g[k] % p == 0);
      assert (exists k :: 0 <= k < |g| && g[k] % p != 0);
      assert false;
    }
  }
  assert g[j] % p != 0;

  result := i + j;
  assert 0 <= result;
  assert result < |f| + |g| by {
    assert i < |f|;
    assert j < |g|;
    assert i + j < |f| + |g|;
  }
}
// </vc-code>

