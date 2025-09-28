// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): modular addition wrap lemma */
lemma ModAddWrap(i: int, n: int, s: int)
  requires n > 0
  requires 0 <= s <= n
  requires 0 <= i < n
  ensures (if i < n - s then (i + s) % n == i + s else (i + s) % n == i + s - n)
{
  if i < n - s {
    assert i + s < n;
    assert (i + s) % n == i + s;
  } else {
    assert i + s >= n;
    assert i + s < 2 * n;
    assert (i + s) % n == i + s - n;
  }
}

/* helper modified by LLM (iteration 5): modular subtraction wrap lemma to compute inverse index */
lemma ModSubWrap(j: int, n: int, s: int)
  requires n > 0
  requires 0 <= s <= n
  requires 0 <= j < n
  ensures 0 <= ((j - s + n) % n) < n && (((j - s + n) % n) + s) % n == j
{
  if j >= s {
    // (j - s + n) % n == j - s
    assert 0 <= j - s < n;
    assert (j - s + n) % n == j - s;
    assert 0 <= (j - s + n) % n < n;
    assert (((j - s + n) % n) + s) % n == (j - s + s) % n;
    assert (j) % n == j;
    assert (((j - s + n) % n) + s) % n == j;
  } else {
    // j < s => j - s + n in [0,n)
    assert 0 <= j - s + n < n;
    assert (j - s + n) % n == j - s + n;
    assert 0 <= (j - s + n) % n < n;
    assert (((j - s + n) % n) + s) % n == (j - s + n + s) % n;
    assert (j - s + n + s) % n == j % n;
    assert j % n == j;
    assert (((j - s + n) % n) + s) % n == j;
  }
}

/* helper modified by LLM (iteration 5): proved properties of rotated sequence using modular lemmas */
lemma RotateSeqProperties(x: seq<real>, s: int)
  requires |x| > 0
  requires 0 <= s <= |x|
  ensures |x[s..] + x[..s]| == |x|
  ensures forall i :: 0 <= i < |x| ==> (x[s..] + x[..s])[i] == x[(i + s) % |x|]
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && (x[s..] + x[..s])[k] == x[j]
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && (x[s..] + x[..s])[k] == x[j]
  ensures multiset(x[s..] + x[..s]) == multiset(x)
{
  var n := |x|;
  var r := x[s..] + x[..s];
  assert |r| == n;
  assert |x[s..]| == n - s;
  assert |x[..s]| == s;

  // Prove r[i] == x[(i + s) % n] for all i by iteration
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall t :: 0 <= t < i ==> r[t] == x[(t + s) % n]
  {
    if i < n - s {
      assert r[i] == x[s + i];
      ModAddWrap(i, n, s);
      assert (i + s) % n == i + s;
      assert x[s + i] == x[(i + s) % n];
    } else {
      assert r[i] == x[i - (n - s)];
      ModAddWrap(i, n, s);
      assert (i + s) % n == i + s - n;
      assert x[i - (n - s)] == x[(i + s) % n];
    }
    i := i + 1;
  }
  assert forall i :: 0 <= i < n ==> r[i] == x[(i + s) % n];

  // For every original index j provide an explicit witness k in the rotated sequence using modular inverse
  var j := 0;
  while j < n
    invariant 0 <= j <= n
  {
    var k := (j - s + n) % n;
    ModSubWrap(j, n, s);
    assert 0 <= k < n;
    // r[k] == x[(k + s) % n] and ModSubWrap ensures (k + s) % n == j
    assert r[k] == x[j];
    assert exists k0 :: 0 <= k0 < n && k0 == k && r[k0] == x[j];
    j := j + 1;
  }
  assert forall j0 :: 0 <= j0 < n ==> exists k0 :: 0 <= k0 < n && r[k0] == x[j0];

  // For every output index k provide an explicit witness j in the original sequence
  var kk := 0;
  while kk < n
    invariant 0 <= kk <= n
  {
    var j0 := (kk + s) % n;
    assert 0 <= j0 < n;
    assert r[kk] == x[j0];
    assert exists j1 :: 0 <= j1 < n && j1 == j0 && r[kk] == x[j1];
    kk := kk + 1;
  }
  assert forall k0 :: 0 <= k0 < n ==> exists j0 :: 0 <= j0 < n && r[k0] == x[j0];

  // Multiset equality follows from concatenation properties
  assert multiset(r) == multiset(x[s..]) + multiset(x[..s]);
  assert x == x[..s] + x[s..];
  assert multiset(x) == multiset(x[..s]) + multiset(x[s..]);
  assert multiset(r) == multiset(x);
}

// </vc-helpers>

// <vc-spec>
method FFTShift(x: seq<real>) returns (result: seq<real>)
  requires |x| >= 0
  ensures |result| == |x|
  // Main transformation: each element at position i comes from position (i + |x| - |x|/2) % |x|
  ensures |x| > 0 ==> forall i :: 0 <= i < |x| ==> 
    result[i] == x[(i + |x| - |x|/2) % |x|]
  // Bijective property: every input element appears exactly once in output
  ensures forall j :: 0 <= j < |x| ==> exists k :: 0 <= k < |x| && result[k] == x[j]
  // Inverse bijective property: every output element comes from exactly one input element  
  ensures forall k :: 0 <= k < |x| ==> exists j :: 0 <= j < |x| && result[k] == x[j]
  // Multiset equality: same elements with same multiplicities
  ensures multiset(result) == multiset(x)
  // Handle empty sequence case
  ensures |x| == 0 ==> result == []
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implemented FFTShift using rotation and invoked lemma */
{
  if |x| == 0 {
    result := [];
    return;
  }
  var n := |x|;
  var s := n - n/2;
  result := x[s..] + x[..s];
  RotateSeqProperties(x, s);
}

// </vc-code>
