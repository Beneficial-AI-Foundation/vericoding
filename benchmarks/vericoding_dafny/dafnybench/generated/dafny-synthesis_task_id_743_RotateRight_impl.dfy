method RotateRight(l: seq<int>, n: int) returns (r: seq<int>)
    requires n >= 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[(i - n + |l|) % |l|]
// </vc-spec>
// <vc-code>
{
  if |l| == 0 {
    r := [];
  } else {
    var effective_n := n % |l|;
    r := seq(|l|, i => l[(i - effective_n + |l|) % |l|]);
    
    // Prove the postcondition holds
    forall i | 0 <= i < |l|
      ensures r[i] == l[(i - n + |l|) % |l|]
    {
      assert r[i] == l[(i - effective_n + |l|) % |l|];
      ModuloEquivalence(i, n, effective_n, |l|);
      assert (i - effective_n + |l|) % |l| == (i - n + |l|) % |l|;
    }
  }
}
// </vc-code>
// <vc-helpers>
lemma ModuloEquivalence(i: int, n: int, effective_n: int, len: int)
    requires len > 0
    requires effective_n == n % len
    requires 0 <= i < len
    ensures (i - effective_n + len) % len == (i - n + len) % len
{
    // Use the fact that (a - b) % m == (a - (b % m)) % m when a >= 0
    assert effective_n >= 0 && effective_n < len;
    assert i - effective_n + len >= 0;
    assert i - n + len >= 0 || i - n + len < 0;
    
    if i - n + len >= 0 {
        // Both expressions are equivalent by modular arithmetic
        var k := n / len;
        assert n == k * len + effective_n;
        
        calc {
            (i - n + len) % len;
            ==
            (i - (k * len + effective_n) + len) % len;
            ==
            (i - effective_n + len - k * len) % len;
            ==
            (i - effective_n + len) % len;
        }
    } else {
        // Handle negative case
        var k := n / len;
        assert n == k * len + effective_n;
        assert k >= 1; // since i - n + len < 0 and i >= 0, len > 0
        
        calc {
            (i - n + len) % len;
            ==
            (i - (k * len + effective_n) + len) % len;
            ==
            (i - effective_n + len - k * len) % len;
            ==
            (i - effective_n + len) % len;
        }
    }
}
// </vc-helpers>