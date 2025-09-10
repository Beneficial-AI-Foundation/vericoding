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
        var t := seqMin(s[1..]);
        if s[0] <= t then s[0] else t
}

function seqMax(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0]
    else
        var t := seqMax(s[1..]);
        if s[0] >= t then s[0] else t
}

function minOpsInRange(s: seq<int>, lo: int, hi: int): int
    requires |s| > 0
    requires lo <= hi
    decreases hi - lo
{
    if lo == hi then sumAbsDifferencesFromTarget(s, lo)
    else
        var a := minOpsInRange(s, lo, hi - 1);
        var b := sumAbsDifferencesFromTarget(s, hi);
        if a <= b then a else b
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
  if !(forall i, j :: 0 <= i < n && 0 <= j < m ==> matrix[i][j] % d == matrix[0][0] % d) {
    result := -1;
    return;
  }
  var flat := flatten(matrix);
  var simplified := divideSequenceByD(flat, d);
  result := minimumOperationsToMakeEqual(simplified);
}
// </vc-code>

