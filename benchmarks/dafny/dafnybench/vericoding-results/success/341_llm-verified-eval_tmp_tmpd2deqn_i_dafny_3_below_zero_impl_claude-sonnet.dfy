function sum(s: seq<int>, n: nat): int
    requires n <= |s|
{
    if |s| == 0 || n == 0 then
        0
    else
        s[0] + sum(s[1..], n-1)
}

// <vc-helpers>
lemma sum_prefix_property(s: seq<int>, i: nat, j: nat)
    requires i <= j <= |s|
    ensures sum(s, j) == sum(s, i) + sum(s[i..], j - i)
{
    if i == 0 {
        assert sum(s, j) == sum(s[0..], j);
        assert s[0..] == s;
    } else if i == j {
        assert sum(s, i) == sum(s, j);
        assert sum(s[i..], 0) == 0;
    } else {
        sum_prefix_property(s[1..], i-1, j-1);
    }
}

lemma sum_monotonic(s: seq<int>, n: nat, m: nat)
    requires n <= m <= |s|
    ensures sum(s, m) == sum(s, n) + sum(s[n..], m - n)
{
    sum_prefix_property(s, n, m);
}

lemma sum_step(s: seq<int>, i: nat)
    requires i < |s|
    ensures sum(s, i + 1) == sum(s, i) + s[i]
{
    if i == 0 {
        assert sum(s, 1) == s[0] + sum(s[1..], 0);
        assert sum(s[1..], 0) == 0;
        assert sum(s, 0) == 0;
    } else {
        sum_step(s[1..], i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method below_zero(ops: seq<int>) returns (result: bool)
    ensures result <==> exists n: nat :: n <= |ops| && sum(ops, n) < 0
// </vc-spec>
// <vc-code>
{
    result := false;
    var balance := 0;
    var i := 0;
    
    while i < |ops|
        invariant 0 <= i <= |ops|
        invariant balance == sum(ops, i)
        invariant result ==> exists n: nat :: n <= i && sum(ops, n) < 0
        invariant !result ==> forall n: nat :: n <= i ==> sum(ops, n) >= 0
    {
        if balance < 0 {
            result := true;
            break;
        }
        balance := balance + ops[i];
        i := i + 1;
        sum_step(ops, i - 1);
        if balance < 0 {
            result := true;
            break;
        }
    }
}
// </vc-code>

