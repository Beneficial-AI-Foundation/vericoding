// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added precondition based on the context of the benches parameter from solve's requires clause, that ensures `n > 0` before calculating `max_seq(benches)`. Also the helper now uses this precondition for the division by n. */
function calculate_minimum_m(n: nat, m: nat, benches: seq<nat>): nat
    requires n > 0 && |benches| == n
{
    var total_sum_benches := sum_seq(benches);
    var max_bench := max_seq(benches);

    var total := total_sum_benches + m;

    if total <= max_bench * n then max_bench
    else (total + n - 1) / n
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
/* code modified by LLM (iteration 2): Added assertion for `|benches| > 0` since `max_seq` requires a non-empty sequence and assigned variables with results from helper function. */
{
  assert |benches| > 0; // Ensures the precondition for max_seq(benches)
  var current_max := max_seq(benches);
  maximum := current_max + m;
  minimum := calculate_minimum_m(n, m, benches);
}
// </vc-code>
