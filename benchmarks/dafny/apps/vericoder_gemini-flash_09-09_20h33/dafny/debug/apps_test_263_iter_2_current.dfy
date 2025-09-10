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
function min_max(a: nat, b: nat): nat
{
  if a < b then a else b
}

function max_of_two(a: nat, b: nat): nat
{
    if a > b then a
    else b
}

lemma lemma_max_seq_positive(s: seq<nat>)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures max_seq(s) > 0
{
    if |s| == 1 {
    } else {
        if s[0] >= max_seq(s[1..]) {
            assert s[0] > 0;
        } else {
            lemma_max_seq_positive(s[1..]);
        }
    }
}

lemma lemma_sum_seq_positive(s: seq<nat>)
    requires forall i :: 0 <= i < |s| ==> s[i] > 0
    ensures sum_seq(s) >= |s|
{
    if |s| == 0 {
    } else {
        lemma_sum_seq_positive(s[1..]);
        assert s[0] > 0;
        assert sum_seq(s[1..]) >= |s[1..]|;
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
    maximum := max_seq(benches) + m;

    var total_sum_benches := sum_seq(benches);
    var current_max_benches := max_seq(benches);

    var total := total_sum_benches + m;

    lemma_max_seq_positive(benches);
    lemma_sum_seq_positive(benches);

    if total_sum_benches + m <= current_max_benches * n then {
        minimum := current_max_benches;
    } else {
        minimum := (total_sum_benches + m + n - 1) / n;
    }
}
// </vc-code>

