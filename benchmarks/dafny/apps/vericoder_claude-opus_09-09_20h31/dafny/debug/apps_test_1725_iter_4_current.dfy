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
    else 
        var restMin := seqMin(s[1..]);
        if s[0] <= restMin then s[0] else restMin
}

function seqMax(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else 
        var restMax := seqMax(s[1..]);
        if s[0] >= restMax then s[0] else restMax
}

function minOpsInRange(s: seq<int>, minVal: int, maxVal: int): int
    requires |s| > 0
    requires minVal <= maxVal
    decreases maxVal - minVal + 1
{
    if minVal == maxVal then
        sumAbsDifferencesFromTarget(s, minVal)
    else
        var opsAtMin := sumAbsDifferencesFromTarget(s, minVal);
        var restOps := minOpsInRange(s, minVal + 1, maxVal);
        if opsAtMin <= restOps then opsAtMin else restOps
}

lemma AllElementsSameRemainderImpliesAllSameRemainder(matrix: seq<seq<int>>, d: int, r: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
    requires forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| ==> matrix[i][j] % d == r
    ensures AllSameRemainder(matrix, d)
{
    // If all elements have remainder r, then any two elements have the same remainder
    forall i, j, k, l | 0 <= i < |matrix| && 0 <= j < |matrix[0]| && 
                        0 <= k < |matrix| && 0 <= l < |matrix[0]|
    ensures matrix[i][j] % d == matrix[k][l] % d
    {
        assert matrix[i][j] % d == r;
        assert matrix[k][l] % d == r;
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
    // Check if all elements have the same remainder when divided by d
    var firstRemainder := matrix[0][0] % d;
    var allSame := true;
    
    var i := 0;
    while i < n && allSame
        invariant 0 <= i <= n
        invariant allSame ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < m ==> matrix[ii][jj] % d == firstRemainder
        invariant !allSame ==> exists ii, jj :: 0 <= ii < n && 0 <= jj < m && matrix[ii][jj] % d != firstRemainder
    {
        var j := 0;
        while j < m && allSame
            invariant 0 <= j <= m
            invariant allSame ==> forall jj :: 0 <= jj < j ==> matrix[i][jj] % d == firstRemainder
            invariant allSame ==> forall ii, jj :: 0 <= ii < i && 0 <= jj < m ==> matrix[ii][jj] % d == firstRemainder
            invariant !allSame ==> exists ii, jj :: 0 <= ii < n && 0 <= jj < m && matrix[ii][jj] % d != firstRemainder
        {
            if matrix[i][j] % d != firstRemainder {
                allSame := false;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    if !allSame {
        // We found an element with a different remainder
        assert exists ii, jj :: 0 <= ii < n && 0 <= jj < m && matrix[ii][jj] % d != firstRemainder;
        assert matrix[0][0] % d == firstRemainder;
        assert !AllSameRemainder(matrix, d);
        return -1;
    }
    
    // All elements have the same remainder, proceed with calculation
    assert allSame;
    assert i == n;
    assert forall ii, jj :: 0 <= ii < n && 0 <= jj < m ==> matrix[ii][jj] % d == firstRemainder;
    AllElementsSameRemainderImpliesAllSameRemainder(matrix, d, firstRemainder);
    assert AllSameRemainder(matrix, d);
    
    var flat := flatten(matrix);
    var simplified := divideSequenceByD(flat, d);
    result := minimumOperationsToMakeEqual(simplified);
}
// </vc-code>

