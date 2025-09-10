predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

// <vc-helpers>
function method SumBelowTail(m: seq<int>, dm: seq<int>, acc: int): int
    requires |m| == |dm|
    ensures SumBelowTail(m, dm, acc) == acc + SumBelow(m, dm)
{
    if |m| == 0 then acc
    else SumBelowTail(m[1..], dm[1..], acc + (dm[0] - 1 - m[0]))
}

lemma {:axiom} SumBelowCorrect(m: seq<int>, dm: seq<int>)
    requires |m| == |dm|
    ensures SumBelow(m, dm) == SumBelowTail(m, dm, 0)
{
}

function MinValidDmAt(m: seq<int>, index: int): int
    requires 0 <= index < |m|
    requires forall i :: 0 <= i < |m| ==> 0 <= m[i] < i + 1
    ensures MinValidDmAt(m, index) == m[index] + 1
{
    m[index] + 1
}

function MinValidDm(m: seq<int>): seq<int>
    requires forall i :: 0 <= i < |m| ==> 0 <= m[i] < i + 1
    ensures |MinValidDm(m)| == |m|
    ensures forall i :: 0 <= i < |m| ==> MinValidDm(m)[i] == MinValidDmAt(m, i)
    ensures forall i :: 0 <= i < |m| ==> MinValidDm(m)[i] >= m[i] + 1
    ensures forall i :: 0 <= i < |m| - 1 ==> MinValidDm(m)[i] <= MinValidDm(m)[i + 1]
{
    if |m| == 0 then []
    else [MinValidDmAt(m, 0)] + MinValidDm(m[1..])
}

lemma {:axiom} MinValidDmProperties(m: seq<int>)
    requires forall i :: 0 <= i < |m| ==> 0 <= m[i] < i + 1
    ensures ValidSolution(|m|, m, MinValidDm(m))
    ensures (forall dm :: ValidSolution(|m|, m, dm) ==> SumBelow(m, MinValidDm(m)) <= SumBelow(m, dm))
{
}

predicate isPartialSolution(n: int, m: seq<int>, dm: seq<int>, k: int) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < k ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < k - 1 ==> dm[i] <= dm[i + 1])
}

function getMinValue(n: int, m: seq<int>, dm: seq<int>, i: int): int
    requires isPartialSolution(n, m, dm, i)
    requires i < n
    ensures getMinValue(n, m, dm, i) >= m[i] + 1
    ensures i > 0 ==> getMinValue(n, m, dm, i) >= dm[i-1]
{
    if i == 0 then m[i] + 1 else max(m[i] + 1, dm[i-1])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var dm := MinValidDm(m);
    result := SumBelow(m, dm);
}
// </vc-code>

