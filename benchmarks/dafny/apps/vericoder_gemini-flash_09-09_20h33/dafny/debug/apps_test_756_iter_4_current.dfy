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
function findCutoffCorrect(a: seq<int>, index: int, cutoff: int): int
    requires 0 <= index <= |a|
    decreases |a| - index
{
    if index >= |a| then cutoff
    else if a[index] > cutoff then cutoff
    else findCutoffCorrect(a, index + 1, a[index] + 15)
}

lemma findCutoffEquivalent(a: seq<int>, index: int, cutoff: int) returns (fce: int)
    requires 0 <= index <= |a|
    ensures findCutoff(a, index, cutoff) == findCutoffCorrect(a, index, cutoff)
    decreases |a| - index
{
    if index >= |a| then fce := cutoff
    else if a[index] > cutoff then fce := cutoff
    else {
        fce := findCutoffEquivalent(a, index + 1, a[index] + 15);
    }
    return fce;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
    var cutoff := findCutoff(a, 0, 15);
    assert findCutoff(a, 0, 15) == findCutoffCorrect(a, 0, 15) by {
      findCutoffEquivalent(a, 0, 15);
    };
    result := min(90, cutoff);
}
// </vc-code>

