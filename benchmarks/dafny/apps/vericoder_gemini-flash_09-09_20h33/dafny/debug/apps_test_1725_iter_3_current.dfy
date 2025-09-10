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
    ensures forall x :: x in s ==> seqMin(s) <= x
    ensures exists i :: 0 <= i < |s| && s[i] == seqMin(s)
{
    if |s| == 1 then s[0]
    else var restMin := seqMin(s[1..]);
         if s[0] < restMin then s[0] else restMin
}

function seqMax(s: seq<int>): int
    requires |s| > 0
    ensures forall x :: x in s ==> seqMax(s) >= x
    ensures exists i :: 0 <= i < |s| && s[i] == seqMax(s)
{
    if |s| == 1 then s[0]
    else var restMax := seqMax(s[1..]);
         if s[0] > restMax then s[0] else restMax
}

function minOpsInRange(s: seq<int>, lower: int, upper: int): int
    requires |s| > 0
    requires lower <= upper
    ensures minOpsInRange(s, lower, upper) >= 0
{
    if lower == upper then
        sumAbsDifferencesFromTarget(s, lower)
    else
        var mid := lower + (upper - lower) / 2;
        var costMid := sumAbsDifferencesFromTarget(s, mid);
        var costMidPlus1 := sumAbsDifferencesFromTarget(s, mid + 1);

        if costMid <= costMidPlus1 then
            minOpsInRange(s, lower, mid)
        else
            minOpsInRange(s, mid + 1, upper)
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
    if !AllSameRemainder(matrix, d)
    {
        result := -1;
    }
    else
    {
        var flat := flatten(matrix);
        var simplified := divideSequenceByD(flat, d);
        result := minimumOperationsToMakeEqual(simplified);
    }
}
// </vc-code>

