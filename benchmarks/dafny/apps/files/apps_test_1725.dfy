Given an n × m matrix of integers and parameter d, find minimum operations to make all elements equal.
Each operation adds or subtracts d from any element. Return -1 if impossible.

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

function minOpsInRange(simplified: seq<int>, minTarget: int, maxTarget: int): int
    requires |simplified| > 0
    requires minTarget <= maxTarget
    decreases maxTarget - minTarget
{
    if minTarget == maxTarget then
        sumAbsDifferencesFromTarget(simplified, minTarget)
    else
        var opsMin := sumAbsDifferencesFromTarget(simplified, minTarget);
        var opsRest := minOpsInRange(simplified, minTarget + 1, maxTarget);
        if opsMin <= opsRest then opsMin else opsRest
}

method solve(n: int, m: int, d: int, matrix: seq<seq<int>>) returns (result: int)
    requires ValidInput(n, m, d, matrix)
    ensures result == -1 <==> !AllSameRemainder(matrix, d)
    ensures result >= 0 ==> AllSameRemainder(matrix, d)
    ensures result >= 0 ==> (var flat := flatten(matrix); var simplified := divideSequenceByD(flat, d); result == minimumOperationsToMakeEqual(simplified))
{
    var a: seq<int> := [];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |a| == i * m
        invariant forall idx :: 0 <= idx < |a| ==> a[idx] == matrix[idx / m][idx % m]
        invariant forall row, col :: 0 <= row < i && 0 <= col < m ==> a[row * m + col] == matrix[row][col]
    {
        var j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant |a| == i * m + j
            invariant forall idx :: 0 <= idx < |a| ==> a[idx] == matrix[idx / m][idx % m]
            invariant forall row, col :: 0 <= row < i && 0 <= col < m ==> a[row * m + col] == matrix[row][col]
            invariant forall col :: 0 <= col < j ==> a[i * m + col] == matrix[i][col]
        {
            a := a + [matrix[i][j]];
            j := j + 1;
        }
        i := i + 1;
    }

    var remainder := a[0] % d;
    i := 1;
    while i < |a|
        invariant 1 <= i <= |a|
        invariant forall k :: 0 <= k < i ==> a[k] % d == remainder
    {
        if a[i] % d != remainder
        {
            assert a[0] % d != a[i] % d;
            assert a[0] == matrix[0][0];
            assert a[i] == matrix[i / m][i % m];
            assert 0 <= i / m < n && 0 <= i % m < m;
            assert matrix[0][0] % d != matrix[i / m][i % m] % d;
            result := -1;
            return;
        }
        i := i + 1;
    }

    assert forall k :: 0 <= k < |a| ==> a[k] % d == remainder;
    assert forall row, col :: 0 <= row < n && 0 <= col < m ==> matrix[row][col] % d == remainder;

    var simplified: seq<int> := [];
    i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |simplified| == i
        invariant forall k :: 0 <= k < i ==> simplified[k] == a[k] / d
    {
        simplified := simplified + [a[i] / d];
        i := i + 1;
    }

    var minVal := simplified[0];
    var maxVal := simplified[0];
    i := 1;
    while i < |simplified|
        invariant 1 <= i <= |simplified|
        invariant forall k :: 0 <= k < i ==> minVal <= simplified[k] <= maxVal
        invariant exists k :: 0 <= k < i && simplified[k] == minVal
        invariant exists k :: 0 <= k < i && simplified[k] == maxVal
    {
        if simplified[i] < minVal { minVal := simplified[i]; }
        if simplified[i] > maxVal { maxVal := simplified[i]; }
        i := i + 1;
    }

    var minOps := -1;
    var target := minVal;
    while target <= maxVal
        invariant minVal <= target
        invariant minOps == -1 || minOps >= 0
    {
        var ops := 0;
        i := 0;
        while i < |simplified|
            invariant 0 <= i <= |simplified|
            invariant ops >= 0
        {
            var diff := if simplified[i] >= target then simplified[i] - target else target - simplified[i];
            ops := ops + diff;
            i := i + 1;
        }
        if minOps == -1 || ops < minOps
        {
            minOps := ops;
        }
        target := target + 1;
    }

    result := minOps;
}
