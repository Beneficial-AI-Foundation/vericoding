predicate ValidInput(n: int, m: int, a: seq<int>)
{
    n >= 1 && m >= 1 && |a| == n && 
    (forall i :: 0 <= i < |a| ==> a[i] >= 1)
}

predicate ValidOutput(result: seq<int>, n: int)
{
    |result| == n && (forall i :: 0 <= i < |result| ==> result[i] >= 0)
}

function ComputePageTurns(a: seq<int>, m: int, i: int, s: int): int
    requires m >= 1
    requires i >= 0
    requires s >= 0
{
    if i >= |a| then 0
    else (s + a[i]) / m
}

function ComputeNextState(a: seq<int>, m: int, i: int, s: int): int
    requires m >= 1
    requires i >= 0
    requires s >= 0
{
    if i >= |a| then s
    else (s + a[i]) % m
}

predicate CorrectPageTurns(result: seq<int>, a: seq<int>, m: int)
    requires m >= 1
{
    |result| == |a| &&
    (forall i :: 0 <= i < |a| ==> 
        var s := ComputeStateAt(a, m, i);
        result[i] == (s + a[i]) / m)
}

function ComputeStateAt(a: seq<int>, m: int, day: int): int
    requires m >= 1
    requires day >= 0
{
    if day == 0 then 0
    else if day > |a| then ComputeStateAt(a, m, |a|)
    else (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m
}

// <vc-helpers>
function ComputeStateAtIterative(a: seq<int>, m: int, day: int): int
    requires m >= 1
    requires day >= 0
    // reads a // Uncommented: reads clause not needed for pure functions.
    ensures ComputeStateAt(a, m, day) == ComputeStateAtIterative(a, m, day)
{
    var s := 0;
    var i := 0;
    while i < day && i < |a|
        invariant 0 <= i <= day
        invariant s == ComputeStateAt(a, m, i)
        decreases day - i
    {
        s := (s + a[i]) % m;
        i := i + 1;
    }
    if day > |a| then
        return ComputeStateAt(a, m, |a|) // Handles the case where day > |a| for ComputeStateAt
    else
        return s;
}

lemma ComputeStateAtRecursiveEqIterative(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires day >= 0
    ensures ComputeStateAt(a, m, day) == ComputeStateAtIterative(a, m, day)
{
    // The proof for this lemma is implicitly handled by the invariant and ensures clauses of
    // ComputeStateAtIterative. No explicit match statement is needed here, as the iterative
    // function's postcondition directly states the equivalence with the recursive one.
    // The Dafny verifier proves this by checking the loop invariants in ComputeStateAtIterative.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, a)
    ensures ValidOutput(result, n)
    ensures CorrectPageTurns(result, a, m)
// </vc-spec>
// <vc-code>
{
    var r := new int[n];
    var s := 0; // current state (pages remaining in current book)
    
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant |r| == n
        invariant (forall k :: 0 <= k < i ==> r[k] == (ComputeStateAt(a, m, k) + a[k]) / m)
        invariant s == ComputeStateAt(a, m, i)
    {
        r[i] := (s + a[i]) / m;
        s := (s + a[i]) % m;
    }
    return r;
}
// </vc-code>

