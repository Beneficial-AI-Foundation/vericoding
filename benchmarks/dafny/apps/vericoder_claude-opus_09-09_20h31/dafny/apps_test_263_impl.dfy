predicate ValidInput(n: nat, m: nat, benches: seq<nat>)
{
    n > 0 && m > 0 && |benches| == n && forall i :: 0 <= i < n ==> benches[i] > 0
}

function max_seq(s: seq<nat>): nat
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max_seq(s[1..]) then s[0]
    else max_seq(s[1..])
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
lemma max_seq_in_bounds(s: seq<nat>, i: nat)
    requires |s| > 0
    requires 0 <= i < |s|
    ensures s[i] <= max_seq(s)
    decreases |s|
{
    if |s| == 1 {
        assert s[i] == s[0] == max_seq(s);
    } else if i == 0 {
        if s[0] >= max_seq(s[1..]) {
            assert s[i] == s[0] == max_seq(s);
        } else {
            assert s[i] == s[0] <= max_seq(s[1..]) == max_seq(s);
        }
    } else {
        max_seq_in_bounds(s[1..], i-1);
        if s[0] >= max_seq(s[1..]) {
            assert max_seq(s) == s[0] >= max_seq(s[1..]) >= s[1..][i-1] == s[i];
        } else {
            assert max_seq(s) == max_seq(s[1..]) >= s[1..][i-1] == s[i];
        }
    }
}

lemma sum_seq_parts(s: seq<nat>, k: nat)
    requires 0 <= k <= |s|
    ensures sum_seq(s) == sum_seq(s[..k]) + sum_seq(s[k..])
{
    if k == 0 {
        assert s[..k] == [];
        assert s[k..] == s;
    } else if k == |s| {
        assert s[..k] == s;
        assert s[k..] == [];
    } else {
        if k == 1 {
            assert s[..1] == [s[0]];
            assert sum_seq(s[..1]) == s[0];
            assert s[1..] == s[k..];
        } else {
            sum_seq_parts(s[1..], k-1);
            assert s[1..][..k-1] == s[..k][1..];
            assert s[1..][k-1..] == s[k..];
        }
    }
}

lemma max_seq_extend(s: seq<nat>, x: nat)
    requires |s| > 0
    ensures max_seq(s + [x]) == if x >= max_seq(s) then x else max_seq(s)
{
    if |s| == 1 {
        assert s + [x] == [s[0], x];
        if x >= s[0] {
            assert max_seq([s[0], x]) == x;
        } else {
            assert max_seq([s[0], x]) == s[0];
        }
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        max_seq_extend(s[1..], x);
    }
}

lemma sum_seq_extend(s: seq<nat>, x: nat)
    ensures sum_seq(s + [x]) == sum_seq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum_seq([x]) == x;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        sum_seq_extend(s[1..], x);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, benches: seq<nat>) returns (minimum: nat, maximum: nat)
    requires ValidInput(n, m, benches)
    ensures maximum == max_seq(benches) + m
    ensures var total := sum_seq(benches) + m;
            var current_max := max_seq(benches);
            if total <= current_max * n then minimum == current_max
            else minimum == (total + n - 1) / n
// </vc-spec>
// <vc-code>
{
    var total := 0;
    var current_max := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant i > 0 ==> current_max == max_seq(benches[..i])
        invariant total == sum_seq(benches[..i])
    {
        var old_total := total;
        total := total + benches[i];
        
        if i == 0 {
            current_max := benches[i];
            assert benches[..1] == [benches[0]];
            assert max_seq(benches[..1]) == benches[0];
            assert sum_seq(benches[..1]) == benches[0];
        } else {
            assert benches[..i+1] == benches[..i] + [benches[i]];
            max_seq_extend(benches[..i], benches[i]);
            
            if benches[i] > current_max {
                current_max := benches[i];
                assert current_max == max_seq(benches[..i+1]);
            } else {
                assert current_max == max_seq(benches[..i]);
                assert current_max == max_seq(benches[..i+1]);
            }
            
            sum_seq_extend(benches[..i], benches[i]);
            assert total == old_total + benches[i];
            assert total == sum_seq(benches[..i]) + benches[i];
            assert total == sum_seq(benches[..i+1]);
        }
        
        i := i + 1;
    }
    
    assert benches[..n] == benches;
    maximum := current_max + m;
    total := total + m;
    
    if total <= current_max * n {
        minimum := current_max;
    } else {
        minimum := (total + n - 1) / n;
    }
}
// </vc-code>

