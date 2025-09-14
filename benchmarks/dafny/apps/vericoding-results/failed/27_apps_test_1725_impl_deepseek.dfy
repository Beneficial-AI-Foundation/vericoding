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
  ensures forall i :: 0 <= i < |s| ==> seqMin(s) <= s[i]
{
  if |s| == 1 then s[0]
  else
    var minRest := seqMin(s[1..]);
    if s[0] <= minRest then s[0] else minRest
}

function seqMax(s: seq<int>): int
  requires |s| > 0
  ensures forall i :: 0 <= i < |s| ==> seqMax(s) >= s[i]
{
  if |s| == 1 then s[0]
  else
    var maxRest := seqMax(s[1..]);
    if s[0] >= maxRest then s[0] else maxRest
}

function minOpsInRange(s: seq<int>, low: int, high: int): int
  requires |s| > 0
  requires low <= high
  ensures exists target :: low <= target <= high && minOpsInRange(s, low, high) == sumAbsDifferencesFromTarget(s, target)
  decreases high - low
{
  if low == high then
    sumAbsDifferencesFromTarget(s, low)
  else
    var mid := low + (high - low) / 2;
    var costMid := sumAbsDifferencesFromTarget(s, mid);
    var costNext := if mid < high then sumAbsDifferencesFromTarget(s, mid + 1) else costMid + 1;
    if costNext < costMid then
      minOpsInRange(s, mid + 1, high)
    else if mid > low then
      var costPrev := sumAbsDifferencesFromTarget(s, mid - 1);
      if costPrev < costMid then
        minOpsInRange(s, low, mid - 1)
      else
        costMid
    else
      costMid
}

ghost method minOpsInRangeProof(s: seq<int>, low: int, high: int)
  requires |s| > 0
  requires 0 <= low <= high
  ensures exists target :: low <= target <= high && minOpsInRange(s, low, high) == sumAbsDifferencesFromTarget(s, target)
  decreases high - low
{
  if low < high {
    var mid := low + (high - low) / 2;
    var costMid := sumAbsDifferencesFromTarget(s, mid);
    var costNext := if mid < high then sumAbsDifferencesFromTarget(s, mid + 1) else costMid + 1;
    if costNext < costMid {
      minOpsInRangeProof(s, mid + 1, high);
    } else if mid > low {
      var costPrev := sumAbsDifferencesFromTarget(s, mid - 1);
      if costPrev < costMid {
        minOpsInRangeProof(s, low, mid - 1);
      }
    }
  }
}

lemma sumAbsDifferencesFromTargetLemma(s: seq<int>, target: int)
  ensures sumAbsDifferencesFromTarget(s, target) >= 0
{
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
    var flat := flatten(matrix);
    var simplified := divideSequenceByD(flat, d);
    var minVal := seqMin(simplified);
    var maxVal := seqMax(simplified);
    minOpsInRangeProof(simplified, minVal, maxVal);
    result := minOpsInRange(simplified, minVal, maxVal);
    assert result >= 0;
  }
}
// </vc-code>

