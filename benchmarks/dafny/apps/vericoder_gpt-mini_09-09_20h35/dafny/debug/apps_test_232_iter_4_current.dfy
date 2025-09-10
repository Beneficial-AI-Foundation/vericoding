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

// <vc-helpers>
predicate subarray_matches_desired(subarray: seq<nat>, desired: seq<nat>, m: nat)
    requires |desired| == m
{
    forall color {:trigger count_occurrences(subarray, color)} :: 1 <= color <= m ==> count_occurrences(subarray, color) == desired[color-1]
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>) returns (result: string)
    requires ValidInput(n, m, colors, desired)
    ensures result == "YES" <==> exists i, j :: 0 <= i <= j < n && subarray_matches_desired(colors[i..j+1], desired, m)
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall a, b {:trigger subarray_matches_desired(colors[a..b+1], desired, m)} :: 0 <= a < i && a <= b < n ==> !subarray_matches_desired(colors[a..b+1], desired, m)
  {
    var j := i;
    while j < n
      decreases n - j
      invariant i <= j <= n
      invariant 0 <= i <= n
      invariant forall a, b {:trigger subarray_matches_desired(colors[a..b+1], desired, m)} :: 0 <= a < i && a <= b < n ==> !subarray_matches_desired(colors[a..b+1], desired, m)
      invariant forall b {:trigger subarray_matches_desired(colors[i..b+1], desired, m)} :: i <= b < j ==> !subarray_matches_desired(colors[i..b+1], desired, m)
    {
      if subarray_matches_desired(colors[i..j+1], desired, m) {
        return "YES";
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return "NO";
}
// </vc-code>

