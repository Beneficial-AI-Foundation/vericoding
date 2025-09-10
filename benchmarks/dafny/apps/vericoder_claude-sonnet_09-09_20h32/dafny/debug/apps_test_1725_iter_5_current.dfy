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
{
    if |s| == 1 then s[0]
    else if s[0] <= seqMin(s[1..]) then s[0]
    else seqMin(s[1..])
}

function seqMax(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= seqMax(s[1..]) then s[0]
    else seqMax(s[1..])
}

function minOpsInRange(simplified: seq<int>, minVal: int, maxVal: int): int
    requires |simplified| > 0
    decreases maxVal - minVal
{
    if minVal >= maxVal then sumAbsDifferencesFromTarget(simplified, minVal)
    else
        var mid := (minVal + maxVal) / 2;
        var leftOps := sumAbsDifferencesFromTarget(simplified, mid);
        var rightOps := sumAbsDifferencesFromTarget(simplified, mid + 1);
        if leftOps <= rightOps then
            minOpsInRange(simplified, minVal, mid)
        else
            minOpsInRange(simplified, mid + 1, maxVal)
}

lemma FlattenPreservesElements(matrix: seq<seq<int>>)
    requires |matrix| > 0
    requires ValidInput(|matrix|, |matrix[0]|, 1, matrix)
    ensures var flat := flatten(matrix);
            forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| ==>
                exists k :: 0 <= k < |flat| && flat[k] == matrix[i][j]
{
    if |matrix| == 1 {
    } else {
        FlattenPreservesElements(matrix[1..]);
    }
}

lemma AllSameRemainderEquivalence(matrix: seq<seq<int>>, d: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
    ensures AllSameRemainder(matrix, d) <==>
            (var flat := flatten(matrix);
             |flat| > 0 ==> (forall i, j :: 0 <= i < |flat| && 0 <= j < |flat| ==> flat[i] % d == flat[j] % d))
{
    if |matrix| == 0 {
    } else {
        FlattenPreservesElements(matrix);
    }
}

lemma AllSameRemainderCorrectness(matrix: seq<seq<int>>, d: int, firstRemainder: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
    requires |matrix| > 0
    requires firstRemainder == matrix[0][0] % d
    requires forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| ==> matrix[i][j] % d == firstRemainder
    ensures AllSameRemainder(matrix, d)
{
}

lemma FlattenLength(matrix: seq<seq<int>>)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, 1, matrix)
    ensures |flatten(matrix)| == |matrix| * (if |matrix| > 0 then |matrix[0]| else 0)
{
    if |matrix| == 0 {
    } else if |matrix| == 1 {
    } else {
        FlattenLength(matrix[1..]);
    }
}

lemma NotAllSameRemainderWitness(matrix: seq<seq<int>>, d: int, i: int, j: int, firstRemainder: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
    requires 0 <= i < |matrix| && 0 <= j < |matrix[0]|
    requires firstRemainder == matrix[0][0] % d
    requires matrix[i][j] % d != firstRemainder
    ensures !AllSameRemainder(matrix, d)
{
}

lemma DivideSequenceDLength(s: seq<int>, d: int)
    requires d > 0
    ensures |divideSequenceByD(s, d)| == |s|
{
    if |s| == 0 {
    } else {
        DivideSequenceDLength(s[1..], d);
    }
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
    var firstRemainder := matrix[0][0] % d;
    var allSame := true;
    var i := 0;
    var witnessI := 0;
    var witnessJ := 0;
    
    while i < n && allSame
        invariant 0 <= i <= n
        invariant allSame ==> (forall row, col :: 0 <= row < i && 0 <= col < m ==> matrix[row][col] % d == firstRemainder)
        invariant !allSame ==> (0 <= witnessI < n && 0 <= witnessJ < m && matrix[witnessI][witnessJ] % d != firstRemainder)
    {
        var j := 0;
        while j < m && allSame
            invariant 0 <= j <= m
            invariant allSame ==> (forall row, col :: 0 <= row < i && 0 <= col < m ==> matrix[row][col] % d == firstRemainder)
            invariant allSame ==> (forall col :: 0 <= col < j ==> matrix[i][col] % d == firstRemainder)
            invariant !allSame ==> (0 <= witnessI < n && 0 <= witnessJ < m && matrix[witnessI][witnessJ] % d != firstRemainder)
        {
            if matrix[i][j] % d != firstRemainder {
                allSame := false;
                witnessI := i;
                witnessJ := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if !allSame {
        NotAllSameRemainderWitness(matrix, d, witnessI, witnessJ, firstRemainder);
        return -1;
    } else {
        AllSameRemainderCorrectness(matrix, d, firstRemainder);
        
        var flat := flatten(matrix);
        FlattenLength(matrix);
        var simplified := divideSequenceByD(flat, d);
        DivideSequenceDLength(flat, d);
        
        result := minimumOperationsToMakeEqual(simplified);
    }
}
// </vc-code>

