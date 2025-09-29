function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

// <vc-helpers>
lemma sum_lemma(s: seq<int>, n: nat)
    requires n <= |s|
    ensures n == 0 ==> sum(s, n) == 0
    ensures n > 0 ==> sum(s, n) == s[0] + sum(s[1..], n-1)
{
    // This follows directly from the definition of sum
}

lemma sum_incremental(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n+1) == sum(s, n) + s[n]
{
    if n == 0 {
        assert sum(s, 1) == s[0] + sum(s[1..], 0);
        assert sum(s[1..], 0) == 0;
        assert sum(s, 0) == 0;
    } else {
        assert sum(s, n+1) == s[0] + sum(s[1..], n);
        assert sum(s, n) == s[0] + sum(s[1..], n-1);
        sum_incremental(s[1..], n-1);
    }
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var current_sum := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == sum(ops, i)
        invariant forall k: nat :: k <= i ==> sum(ops, k) >= 0
    {
        current_sum := current_sum + ops[i];
        sum_incremental(ops, i);
        i := i + 1;
        
        if current_sum < 0 {
            assert sum(ops, i) < 0;
            assert i <= |ops|;
            return true;
        }
    }
    
    assert i == |ops|;
    assert forall n: nat :: n <= |ops| ==> sum(ops, n) >= 0;
    return false;
}
// </vc-code>

