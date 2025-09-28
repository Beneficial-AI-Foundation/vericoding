// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add missing preconditions to minOpsInRange for seqMin and seqMax calls */
function seqMin(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else var res := seqMin(s[1..]); if s[0] < res then s[0] else res
}

function seqMax(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else var res := seqMax(s[1..]); if s[0] > res then s[0] else res
}

function min(a: int, b: int): int {
    if a < b then a else b
}

function minOpsInRange(simplified: seq<int>, lower: int, upper: int): int
    requires |simplified| > 0
    requires lower <= upper
    requires forall i :: 0 <= i < |simplified| ==> seqMin(simplified) <= simplified[i] <= seqMax(simplified)
    requires lower >= seqMin(simplified)
    requires upper <= seqMax(simplified)
decreases upper - lower
{
    if lower == upper then sumAbsDifferencesFromTarget(simplified, lower)
    else
        min(
            sumAbsDifferencesFromTarget(simplified, lower),
            minOpsInRange(simplified, lower + 1, upper)
        )
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
/* code modified by LLM (iteration 5): Add assertions to prove preconditions of minOpsInRange for recursive call calculation */
{
    if !AllSameRemainder(matrix, d) {
        return -1;
    }

    var flat := flatten(matrix);
    var simplified := divideSequenceByD(flat, d);
    
    // The values in simplified are non-negative because matrix elements are positive and d > 0
    // All simplified[i] are integers by property of integer division

    // Prove that all elements simplified[i] are within the range [seqMin(simplified), seqMax(simplified)]
    assert |simplified| > 0; // follows from |matrix| > 0 and flatten(matrix) retains elements
    var minVal := seqMin(simplified);
    var maxVal := seqMax(simplified);
    assert forall i :: 0 <= i < |simplified| ==> minVal <= simplified[i] <= maxVal;

    return minimumOperationsToMakeEqual(simplified);
}
// </vc-code>
