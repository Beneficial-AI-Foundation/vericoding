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
  var wi: int :| 0 <= wi < |f| && f[wi] % p != 0;
  var i := 0;
  while i < |f| && f[i] % p == 0
    invariant 0 <= i <= |f|
    invariant forall k :: 0 <= k < i ==> f[k] % p == 0
    invariant i <= wi < |f|
    decreases |f| - i
  {
    i := i + 1;
  }
  assert i < |f|;
  assert f[i] % p != 0;

  var wj: int :| 0 <= wj < |g| && g[wj] % p != 0;
  var j := 0;
  while j < |g| && g[j] % p == 0
    invariant 0 <= j <= |g|
    invariant forall k :: 0 <= k < j ==> g[k] % p == 0
    invariant j <= wj < |g|
    decreases |g| - j
  {
    j := j + 1;
  }
  assert j < |g|;
  assert g[j] % p != 0;

  result := i + j;
}
// </vc-code>

