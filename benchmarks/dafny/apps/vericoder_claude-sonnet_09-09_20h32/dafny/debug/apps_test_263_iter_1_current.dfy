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
lemma max_seq_properties(s: seq<nat>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_seq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max_seq(s)
{
    if |s| == 1 {
        assert s[0] == max_seq(s);
    } else {
        max_seq_properties(s[1..]);
        if s[0] >= max_seq(s[1..]) {
            assert max_seq(s) == s[0];
        } else {
            assert max_seq(s) == max_seq(s[1..]);
        }
    }
}

lemma division_ceil_property(a: nat, b: nat)
    requires b > 0
    ensures (a + b - 1) / b * b >= a
    ensures a > 0 ==> (a + b - 1) / b >= (a - 1) / b + 1
{
}

lemma sum_seq_bounds(s: seq<nat>)
    requires |s| > 0
    ensures sum_seq(s) >= max_seq(s)
{
    if |s| == 1 {
        assert sum_seq(s) == s[0] == max_seq(s);
    } else {
        sum_seq_bounds(s[1..]);
        if s[0] >= max_seq(s[1..]) {
            assert max_seq(s) == s[0];
            assert sum_seq(s) == s[0] + sum_seq(s[1..]) >= s[0] == max_seq(s);
        } else {
            assert max_seq(s) == max_seq(s[1..]);
            assert sum_seq(s) == s[0] + sum_seq(s[1..]) >= sum_seq(s[1..]) >= max_seq(s[1..]) == max_seq(s);
        }
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
    var total := sum_seq(benches) + m;
    var current_max := max_seq(benches);
    
    maximum := current_max + m;
    
    if total <= current_max * n {
        minimum := current_max;
    } else {
        minimum := (total + n - 1) / n;
    }
    
    max_seq_properties(benches);
    sum_seq_bounds(benches);
    division_ceil_property(total, n);
}
// </vc-code>

