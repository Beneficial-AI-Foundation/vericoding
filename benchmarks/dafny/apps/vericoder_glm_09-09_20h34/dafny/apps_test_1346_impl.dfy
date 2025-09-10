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
  while i < n && f[i] % p == 0
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> f[k] % p == 0
    decreases n - i
  {
    i := i + 1;
  }
  
  if i == n {
    var k0 :| 0 <= k0 < n && f[k0] % p != 0;
    assert f[k0] % p == 0;
    assert false;
  }
  
  var j := 0;
  while j < m && g[j] % p == 0
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < j ==> g[k] % p == 0
    decreases m - j
  {
    j := j + 1;
  }
  
  if j == m {
    var k0 :| 0 <= k0 < m && g[k0] % p != 0;
    assert g[k0] % p == 0;
    assert false;
  }
  
  return i + j;
}
// </vc-code>

