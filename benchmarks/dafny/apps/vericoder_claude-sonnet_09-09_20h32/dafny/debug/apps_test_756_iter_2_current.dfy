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
lemma findCutoffBounds(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires 1 <= cutoff <= 105
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 90
    ensures 1 <= findCutoff(a, index, cutoff) <= 105
    decreases |a| - index
{
    if index >= |a| {
        // Base case: return cutoff
    } else if a[index] > cutoff {
        // Return cutoff
    } else {
        // Recursive case
        assert 1 <= a[index] <= 90;
        assert 1 <= a[index] + 15 <= 105;
        findCutoffBounds(a, index + 1, a[index] + 15);
    }
}

lemma findCutoffCorrectness(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires forall i :: 0 <= i < |a| ==> 1 <= a[i] <= 90
    ensures findCutoff(a, index, cutoff) == findCutoff(a, 0, cutoff)
    decreases |a| - index
{
    if index == 0 {
        // Base case: trivially true
    } else if index >= |a| {
        // Both return cutoff
    } else {
        // Use induction
        findCutoffCorrectness(a, index - 1, cutoff);
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
    findCutoffBounds(a, 0, 15);
    var cutoffResult := findCutoff(a, 0, 15);
    result := min(90, cutoffResult);
}
// </vc-code>

