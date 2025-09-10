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
lemma FindCutoff_ge15(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires cutoff >= 15
    requires (forall i :: 0 <= i < |a| ==> 1 <= a[i])
    ensures findCutoff(a, index, cutoff) >= 15
    decreases |a| - index
{
    if index >= |a| {
        // then findCutoff returns cutoff which is >= 15
    } else {
        if a[index] > cutoff {
            // findCutoff returns cutoff which is >= 15
        } else {
            // a[index] + 15 >= 1 + 15 = 16 >= 15
            FindCutoff_ge15(a, index + 1, a[index] + 15);
        }
    }
}

lemma Min_preserves_lower_bound(x: int, y: int, lb: int)
    requires x >= lb && y >= lb
    ensures min(x, y) >= lb
{
    if x <= y {
    } else {
    }
}

lemma Min_le_left(x: int, y: int)
    ensures min(x, y) <= x
{
    if x <= y {
    } else {
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
  result := min(90, findCutoff(a, 0, 15));
  FindCutoff_ge15(a, 0, 15);
  Min_preserves_lower_bound(90, findCutoff(a, 0, 15), 15);
  Min_le_left(90, findCutoff(a, 0, 15));
}
// </vc-code>

