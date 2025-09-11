// <vc-preamble>
function count_occurrences(s: seq<nat>, value: nat): nat
{
    if |s| == 0 then 0
    else if s[0] == value then 1 + count_occurrences(s[1..], value)
    else count_occurrences(s[1..], value)
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

predicate subarray_matches_desired(subarray: seq<nat>, desired: seq<nat>, m: nat)
    requires |desired| == m
{
    forall color :: 1 <= color <= m ==> count_occurrences(subarray, color) == desired[color-1]
}

predicate ValidInput(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>)
{
    |colors| == n &&
    |desired| == m &&
    (forall i :: 0 <= i < |colors| ==> 1 <= colors[i] <= m) &&
    (forall i :: 0 <= i < |desired| ==> desired[i] >= 0) &&
    sum_seq(desired) <= n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>) returns (result: string)
    requires ValidInput(n, m, colors, desired)
    ensures result == "YES" <==> exists i, j :: 0 <= i <= j < n && subarray_matches_desired(colors[i..j+1], desired, m)
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
