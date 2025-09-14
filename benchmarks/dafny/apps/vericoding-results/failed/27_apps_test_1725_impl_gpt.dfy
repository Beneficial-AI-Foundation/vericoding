predicate ValidInput(n: int, m: int, d: int, matrix: seq<seq<int>>)
{
    n > 0 && m > 0 && d > 0 &&
    |matrix| == n &&
    (forall i :: 0 <= i < n ==> |matrix[i]| == m) &&
    (forall i, j :: 0 <= i < n && 0 <= j < m ==> matrix[i][j] > 0)
}

predicate AllSameRemainder(matrix: seq<seq<int>>, d: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
{
    forall i, j, k, l :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| && 
                        0 <= k < |matrix| && 0 <= l < |matrix[0]| ==>
        matrix[i][j] % d == matrix[k][l] % d
}

function flatten(matrix: seq<seq<int>>): seq<int>
{
    if |matrix| == 0 then []
    else matrix[0] + flatten(matrix[1..])
}

function divideSequenceByD(s: seq<int>, d: int): seq<int>
    requires d > 0
{
    if |s| == 0 then []
    else [s[0] / d] + divideSequenceByD(s[1..], d)
}

function sumAbsDifferencesFromTarget(s: seq<int>, target: int): int
{
    if |s| == 0 then 0
    else (if s[0] >= target then s[0] - target else target - s[0]) + sumAbsDifferencesFromTarget(s[1..], target)
}

function minimumOperationsToMakeEqual(simplified: seq<int>): int
    requires |simplified| > 0
{
    var minVal := seqMin(simplified);
    var maxVal := seqMax(simplified);
    minOpsInRange(simplified, minVal, maxVal)
}

// <vc-helpers>
function seqMin(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0]
    else
        var m := seqMin(s[1..]);
        if s[0] < m then s[0] else m
}

function seqMax(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0]
    else
        var m := seqMax(s[1..]);
        if s[0] > m then s[0] else m
}

function minOpsInRange(s: seq<int>, a: int, b: int): int
    decreases if a <= b then b - a + 1 else 0
{
    if a > b then 0
    else if a == b then sumAbsDifferencesFromTarget(s, a)
    else
        var rest := minOpsInRange(s, a + 1, b);
        var cur := sumAbsDifferencesFromTarget(s, a);
        if cur < rest then cur else rest
}

lemma lemma_DividePreservesLength(s: seq<int>, d: int)
    requires d > 0
    ensures |divideSequenceByD(s, d)| == |s|
    decreases |s|
{
    if |s| == 0 {
    } else {
        assert divideSequenceByD(s, d) == [s[0] / d] + divideSequenceByD(s[1..], d);
        lemma_DividePreservesLength(s[1..], d);
    }
}

lemma lemma_FlattenNonEmpty_FromValid(n: int, m: int, d: int, matrix: seq<seq<int>>)
    requires ValidInput(n, m, d, matrix)
    ensures |flatten(matrix)| > 0
{
    assert |matrix| == n;
    assert n > 0;
    assert |matrix| > 0;

    assert (forall i :: 0 <= i < n ==> |matrix[i]| == m);
    assert 0 <= 0 < n;
    assert |matrix[0]| == m;
    assert m > 0;
    assert |matrix[0]| > 0;

    assert flatten(matrix) == matrix[0] + flatten(matrix[1..]);
    assert |flatten(matrix)| == |matrix[0] + flatten(matrix[1..])|;
    assert |matrix[0] + flatten(matrix[1..])| == |matrix[0]| + |flatten(matrix[1..])|;
    assert 0 <= |flatten(matrix[1..])|;

    assert |flatten(matrix)| > 0;
}

lemma lemma_AbsMinusNonNeg(x: int, target: int)
    ensures (if x >= target then x - target else target - x) >= 0
{
    if x >= target {
        assert x - target >= 0;
    } else {
        assert target - x >= 0;
    }
}

lemma lemma_SumAbsDifferences_NonNeg(s: seq<int>, target: int)
    ensures sumAbsDifferencesFromTarget(s, target) >= 0
    decreases |s|
{
    if |s| == 0 {
        assert sumAbsDifferencesFromTarget(s, target) == 0;
    } else {
        lemma_SumAbsDifferences_NonNeg(s[1..], target);
        lemma_AbsMinusNonNeg(s[0], target);
        assert sumAbsDifferencesFromTarget(s, target) ==
               (if s[0] >= target then s[0] - target else target - s[0]) + sumAbsDifferencesFromTarget(s[1..], target);
        assert (if s[0] >= target then s[0] - target else target - s[0]) >= 0;
        assert sumAbsDifferencesFromTarget(s[1..], target) >= 0;
    }
}

lemma lemma_minOpsInRange_NonNeg(s: seq<int>, a: int, b: int)
    ensures minOpsInRange(s, a, b) >= 0
    decreases if a <= b then b - a + 1 else 0
{
    if a > b {
        assert minOpsInRange(s, a, b) == 0;
    } else if a == b {
        assert minOpsInRange(s, a, b) == sumAbsDifferencesFromTarget(s, a);
        lemma_SumAbsDifferences_NonNeg(s, a);
    } else {
        lemma_minOpsInRange_NonNeg(s, a + 1, b);
        lemma_SumAbsDifferences_NonNeg(s, a);
        assert minOpsInRange(s, a, b) ==
               (if sumAbsDifferencesFromTarget(s, a) < minOpsInRange(s, a + 1, b)
                then sumAbsDifferencesFromTarget(s, a)
                else minOpsInRange(s, a + 1, b));
        assert minOpsInRange(s, a + 1, b) >= 0;
        assert sumAbsDifferencesFromTarget(s, a) >= 0;
    }
}

lemma lemma_minimumOperationsToMakeEqual_NonNeg(simplified: seq<int>)
    requires |simplified| > 0
    ensures minimumOperationsToMakeEqual(simplified) >= 0
{
    var minVal := seqMin(simplified);
    var maxVal := seqMax(simplified);
    lemma_minOpsInRange_NonNeg(simplified, minVal, maxVal);
    assert minimumOperationsToMakeEqual(simplified) == minOpsInRange(simplified, minVal, maxVal);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, d: int, matrix: seq<seq<int>>) returns (result: int)
    requires ValidInput(n, m, d, matrix)
    ensures result == -1 <==> !AllSameRemainder(matrix, d)
    ensures result >= 0 ==> AllSameRemainder(matrix, d)
    ensures result >= 0 ==> (var flat := flatten(matrix); var simplified := divideSequenceByD(flat, d); result == minimumOperationsToMakeEqual(simplified))
// </vc-spec>
// <vc-code>
{
    if !AllSameRemainder(matrix, d) {
        result := -1;
    } else {
        lemma_FlattenNonEmpty_FromValid(n, m, d, matrix);
        var flat := flatten(matrix);
        var simplified := divideSequenceByD(flat, d);
        lemma_DividePreservesLength(flat, d);
        assert |simplified| == |flat|;
        assert |simplified| > 0;
        lemma_minimumOperationsToMakeEqual_NonNeg(simplified);
        var opt := minimumOperationsToMakeEqual(simplified);
        assert opt >= 0;
        result := opt;
    }
}
// </vc-code>

