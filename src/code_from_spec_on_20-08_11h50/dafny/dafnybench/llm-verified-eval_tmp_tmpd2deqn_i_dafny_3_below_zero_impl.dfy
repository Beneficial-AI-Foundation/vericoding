// <vc-spec>
function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

// <vc-helpers>
lemma sum_prefix_property(s: seq<int>, n: nat)
    requires n < |s|
    ensures sum(s, n+1) == sum(s, n) + s[n]
{
    if n == 0 {
        if |s| == 0 {
            // This case is impossible due to the requires clause
        } else {
            assert sum(s, 1) == s[0] + sum(s[1..], 0);
            assert sum(s[1..], 0) == 0;
            assert sum(s, 0) == 0;
        }
    } else {
        assert sum(s, n+1) == s[0] + sum(s[1..], n);
        assert sum(s, n) == s[0] + sum(s[1..], n-1);
        sum_prefix_property(s[1..], n-1);
        assert sum(s[1..], n) == sum(s[1..], n-1) + s[1..][n-1];
        assert s[1..][n-1] == s[n];
    }
}
// </vc-helpers>

method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var current_sum := 0;
    result := false;
    
    while i <= |ops|
        invariant 0 <= i <= |ops|
        invariant current_sum == sum(ops, i)
        invariant result <==> exists n: nat :: n < i && sum(ops, n) < 0
    {
        if current_sum < 0 {
            result := true;
        }
        
        if i == |ops| {
            break;
        }
        
        sum_prefix_property(ops, i);
        current_sum := current_sum + ops[i];
        i := i + 1;
    }
}
// </vc-code>