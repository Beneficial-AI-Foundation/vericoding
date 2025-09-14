predicate ValidInput(n: int, a: seq<int>) {
    n >= 1 && n <= 90 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= 90) &&
    (forall i :: 0 <= i < n - 1 ==> a[i] < a[i + 1])
}

function findCutoff(a: seq<int>, index: int, cutoff: int): int
    requires 0 <= index <= |a|
    decreases |a| - index
{
    if index >= |a| then cutoff
    else if a[index] > cutoff then cutoff
    else findCutoff(a, index + 1, a[index] + 15)
}

function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidOutput(result: int, n: int, a: seq<int>) {
    ValidInput(n, a) ==>
    (1 <= result <= 90 &&
     result == min(90, findCutoff(a, 0, 15)))
}

// <vc-helpers>
lemma findCutoff_maintains_lower_bound(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    requires cutoff >= 1
    ensures findCutoff(a, index, cutoff) >= 1
    decreases |a| - index
{
    if index < |a| && a[index] <= cutoff {
        findCutoff_maintains_lower_bound(a, index + 1, a[index] + 15);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
    findCutoff_maintains_lower_bound(a, 0, 15);
    var fc := findCutoff(a, 0, 15);
    result := min(90, fc);
}
// </vc-code>

