// <vc-preamble>
predicate ValidInput(a: seq<int>, b: seq<int>, n: int)
{
    |a| >= 0 && |b| >= 0 &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 0) &&
    (forall j :: 0 <= j < |b| ==> b[j] >= 0) &&
    n >= 1
}

function sum_seq(s: seq<int>): int
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

function ShelvesNeeded(total: int, capacity: int): int
    requires capacity > 0
{
    if total == 0 then 0 else (total - 1) / capacity + 1
}

predicate CanPlaceAll(a: seq<int>, b: seq<int>, n: int)
    requires ValidInput(a, b, n)
{
    var total_cups := sum_seq(a);
    var total_medals := sum_seq(b);
    var shelves_for_cups := ShelvesNeeded(total_cups, 5);
    var shelves_for_medals := ShelvesNeeded(total_medals, 10);
    shelves_for_cups + shelves_for_medals <= n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>, n: int) returns (result: string)
    requires ValidInput(a, b, n)
    ensures result == (if CanPlaceAll(a, b, n) then "YES" else "NO")
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
