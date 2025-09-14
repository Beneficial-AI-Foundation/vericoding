function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

// <vc-helpers>
// Updated helpers: none required for the fixed implementation.
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
  var k: nat := 0;
  var found := false;
  var w: nat := 0;
  while k <= |ops| && !found
    invariant k <= |ops| + 1
    invariant forall j: nat :: j < k ==> sum(ops, j) >= 0
    invariant found ==> w <= |ops| && sum(ops, w) < 0
    decreases (if !found then |ops| + 1 - k else 0)
  {
    if sum(ops, k) < 0 {
      w := k;
      found := true;
    } else {
      k := k + 1;
    }
  }
  if found {
    assert w <= |ops| && sum(ops, w) < 0;
    return true;
  } else {
    // From exit we have !(k <= |ops| && !found) and invariant k <= |ops|+1,
    // so here !found implies k > |ops| and thus k == |ops| + 1.
    assert k > |ops|;
    assert k <= |ops| + 1;
    assert k == |ops| + 1;
    // Use the loop invariant forall j < k ==> sum(...) >= 0 to show for all j <= |ops|.
    var j := 0;
    while j <= |ops|
      decreases |ops| - j
    {
      assert j < k;
      assert sum(ops, j) >= 0;
      j := j + 1;
    }
    return false;
  }
}
// </vc-code>

