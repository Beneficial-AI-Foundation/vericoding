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
    requires cutoff <= 90
    ensures findCutoff(a, index, cutoff) == min(90, findCutoff(a, index, cutoff))
    decreases |a| - index
{
    // The lemma is trivial because min(90, x) == min(90, min(90, x))
    // But we need to prove that findCutoff(a, index, cutoff) <= 90
    if index < |a| && a[index] <= cutoff {
        var new_cutoff := a[index] + 15;
        assert new_cutoff <= 90; // Since a[index] <= cutoff <= 90 and a[i] <= 90
        findCutoffLemma(a, index + 1, new_cutoff);
    }
}

lemma findCutoffMonotonic(a: seq<int>, index: int, cutoff1: int, cutoff2: int)
    requires 0 <= index <= |a|
    requires cutoff1 <= cutoff2
    requires cutoff2 <= 90
    ensures findCutoff(a, index, cutoff1) <= findCutoff(a, index, cutoff2)
    decreases |a| - index
{
    if index < |a| {
        if a[index] > cutoff1 && a[index] > cutoff2 {
            // Both cutoffs are less than a[index], so both return their respective cutoffs
            assert findCutoff(a, index, cutoff1) == cutoff1;
            assert findCutoff(a, index, cutoff2) == cutoff2;
        } else if a[index] <= cutoff1 && a[index] <= cutoff2 {
            // Both proceed with recursive call
            var new_cutoff := a[index] + 15;
            assert new_cutoff <= 90; // Since a[index] <= cutoff2 <= 90
            findCutoffMonotonic(a, index + 1, new_cutoff, new_cutoff);
        } else if a[index] <= cutoff1 {
            // cutoff1 proceeds, cutoff2 returns cutoff2
            assert findCutoff(a, index, cutoff2) == cutoff2;
            var new_cutoff := a[index] + 15;
            assert new_cutoff <= 90; // Since a[index] <= cutoff1 <= cutoff2 <= 90
            findCutoffLemma(a, index + 1, new_cutoff);
            assert findCutoff(a, index, cutoff1) <= 90;
        } else {
            // cutoff2 proceeds, cutoff1 returns cutoff1
            assert findCutoff(a, index, cutoff1) == cutoff1;
            var new_cutoff := a[index] + 15;
            assert new_cutoff <= 90; // Since a[index] <= cutoff2 <= 90
            findCutoffLemma(a, index + 1, new_cutoff);
            assert findCutoff(a, index, cutoff2) <= 90;
            assert cutoff1 <= cutoff2;
        }
    } else {
        assert findCutoff(a, index, cutoff1) == cutoff1;
        assert findCutoff(a, index, cutoff2) == cutoff2;
    }
}

lemma findCutoffRange(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires cutoff <= 90
    ensures findCutoff(a, index, cutoff) <= 90
    decreases |a| - index
{
    if index < |a| && a[index] <= cutoff {
        var new_cutoff := a[index] + 15;
        assert new_cutoff <= 90; // Since a[index] <= 90
        findCutoffRange(a, index + 1, new_cutoff);
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
        findCutoffRange(a, i, cutoff);
    }
    findCutoffLemma(a, i, cutoff);
    result := min(90, cutoff);
}
// </vc-code>

