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
lemma LemmaFindFirstNonZeroIndex(s: seq<int>, p: int)
  requires |s| > 0
  requires p != 0
  requires exists k :: 0 <= k < |s| && s[k] % p != 0
  ensures exists i :: 0 <= i < |s| && s[i] % p != 0 && (forall k :: 0 <= k < i ==> s[k] % p == 0)
{
  var i := 0;
  while i < |s| && s[i] % p == 0
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] % p == 0
  {
    i := i + 1;
  }
  assert i < |s| && s[i] % p != 0;
}

lemma LemmaSumBounds(i: int, j: int, n: int, m: int)
  requires 0 <= i < n
  requires 0 <= j < m
  ensures 0 <= i + j < n + m
{
}
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
  {
    i := i + 1;
  }
  
  var j := 0;
  while j < m && g[j] % p == 0
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < j ==> g[k] % p == 0
  {
    j := j + 1;
  }
  
  result := i + j;
  LemmaSumBounds(i, j, n, m);
}
// </vc-code>

