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
lemma findCutoffLemma(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    ensures findCutoff(a, index, cutoff) == min(90, findCutoff(a, index, cutoff))
    decreases |a| - index
{
    if index < |a| && a[index] <= cutoff {
        findCutoffLemma(a, index + 1, a[index] + 15);
    }
}

lemma findCutoffMonotonic(a: seq<int>, index: int, cutoff1: int, cutoff2: int)
    requires 0 <= index <= |a|
    requires cutoff1 <= cutoff2
    ensures findCutoff(a, index, cutoff1) <= findCutoff(a, index, cutoff2)
    decreases |a| - index
{
    if index < |a| {
        if a[index] > cutoff1 && a[index] > cutoff2 {
            // Both cutoffs are less than a[index], so both return their respective cutoffs
        } else if a[index] <= cutoff1 && a[index] <= cutoff2 {
            // Both proceed with recursive call
            findCutoffMonotonic(a, index + 1, a[index] + 15, a[index] + 15);
        } else if a[index] <= cutoff1 {
            // cutoff1 proceeds, cutoff2 returns cutoff2
            assert findCutoff(a, index, cutoff2) == cutoff2;
        } else {
            // cutoff2 proceeds, cutoff1 returns cutoff1
            assert findCutoff(a, index, cutoff1) == cutoff1;
        }
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
    var cutoff := 15;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant cutoff == findCutoff(a, i, cutoff)
        invariant cutoff <= 90
    {
        if a[i] > cutoff {
            break;
        }
        cutoff := a[i] + 15;
        i := i + 1;
    }
    result := min(90, cutoff);
    findCutoffLemma(a, i, cutoff);
}
// </vc-code>

