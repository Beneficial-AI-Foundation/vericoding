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
lemma ValidSolutionExists(n: int, m: seq<int>)
    requires ValidInput(n, m)
    ensures exists dm :: ValidSolution(n, m, dm)
{
    var dm := ComputeDM(n, m);
    assert ValidSolution(n, m, dm);
}

function ComputeDM(n: int, m: seq<int>): seq<int>
    requires ValidInput(n, m)
    ensures |ComputeDM(n, m)| == n
    ensures ValidSolution(n, m, ComputeDM(n, m))
{
    ComputeDMHelper(m, 0)
}

function ComputeDMHelper(m: seq<int>, prev: int): seq<int>
    requires |m| > 0
    ensures |ComputeDMHelper(m, prev)| == |m|
    ensures forall i :: 0 <= i < |m| ==> ComputeDMHelper(m, prev)[i] >= m[i] + 1
    ensures forall i :: 0 <= i < |m| - 1 ==> ComputeDMHelper(m, prev)[i] <= ComputeDMHelper(m, prev)[i + 1]
    ensures prev <= ComputeDMHelper(m, prev)[0]
{
    var first := if m[0] + 1 >= prev then m[0] + 1 else prev;
    if |m| == 1 then
        [first]
    else
        [first] + ComputeDMHelper(m[1..], first)
}

function ComputeSum(m: seq<int>): int
    requires |m| > 0
{
    ComputeSumHelper(m, 0)
}

function ComputeSumHelper(m: seq<int>, prev: int): int
    requires |m| > 0
{
    var first := if m[0] + 1 >= prev then m[0] + 1 else prev;
    var contribution := first - 1 - m[0];
    if |m| == 1 then
        contribution
    else
        contribution + ComputeSumHelper(m[1..], first)
}

lemma ComputeSumCorrect(n: int, m: seq<int>)
    requires ValidInput(n, m)
    ensures ComputeSum(m) == SumBelow(m, ComputeDM(n, m))
{
    var dm := ComputeDM(n, m);
    ComputeSumHelperCorrect(m, 0, dm);
}

lemma ComputeSumHelperCorrect(m: seq<int>, prev: int, dm: seq<int>)
    requires |m| > 0
    requires |dm| == |m|
    requires dm == ComputeDMHelper(m, prev)
    ensures ComputeSumHelper(m, prev) == SumBelow(m, dm)
{
    var first := if m[0] + 1 >= prev then m[0] + 1 else prev;
    assert dm[0] == first;
    
    if |m| == 1 {
        assert ComputeSumHelper(m, prev) == first - 1 - m[0];
        assert SumBelow(m, dm) == dm[0] - 1 - m[0];
        assert dm[0] == first;
    } else {
        assert dm[1..] == ComputeDMHelper(m[1..], first);
        ComputeSumHelperCorrect(m[1..], first, dm[1..]);
    }
}

lemma SumBelowNonNegative(m: seq<int>, dm: seq<int>)
    requires |m| == |dm|
    requires forall i :: 0 <= i < |m| ==> dm[i] >= m[i] + 1
    ensures SumBelow(m, dm) >= 0
{
    if |m| == 0 {
        assert SumBelow(m, dm) == 0;
    } else {
        assert dm[0] >= m[0] + 1;
        assert dm[0] - 1 - m[0] >= 0;
        SumBelowNonNegative(m[1..], dm[1..]);
        assert SumBelow(m, dm) == (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..]);
        assert SumBelow(m[1..], dm[1..]) >= 0;
        assert SumBelow(m, dm) >= 0;
    }
}

lemma ComputeSumNonNegative(n: int, m: seq<int>)
    requires ValidInput(n, m)
    ensures ComputeSum(m) >= 0
{
    var dm := ComputeDM(n, m);
    assert ValidSolution(n, m, dm);
    assert forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1;
    SumBelowNonNegative(m, dm);
    ComputeSumCorrect(n, m);
    assert ComputeSum(m) == SumBelow(m, dm);
    assert ComputeSum(m) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    result := ComputeSum(m);
    ComputeSumNonNegative(n, m);
    assert result >= 0;
}
// </vc-code>

