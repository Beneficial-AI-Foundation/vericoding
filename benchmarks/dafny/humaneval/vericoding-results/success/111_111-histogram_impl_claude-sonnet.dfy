// <vc-preamble>
type BiggestMap = map<int, int>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Simplified helper functions */
function CountOccurrences(a: seq<int>, val: int): int {
  |set j | 0 <= j < |a| && a[j] == val|
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)

  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed loop invariant syntax and logic */
{
  biggest := map[];
  if |a| == 0 {
    return;
  }
  
  // First pass: find maximum count
  var maxCount := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant maxCount >= 0
    invariant forall k :: 0 <= k < i ==> CountOccurrences(a, a[k]) <= maxCount
    invariant maxCount == 0 || exists k :: 0 <= k < |a| && CountOccurrences(a, a[k]) >= maxCount
  {
    var count := CountOccurrences(a, a[i]);
    if count > maxCount {
      maxCount := count;
    }
    i := i + 1;
  }
  
  // Second pass: collect all elements with maximum count
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < i && CountOccurrences(a, a[k]) == maxCount ==> a[k] in biggest && biggest[a[k]] == maxCount
    invariant forall v :: v in biggest ==> biggest[v] == maxCount
    invariant forall v :: v in biggest ==> CountOccurrences(a, v) == maxCount
    invariant forall k :: 0 <= k < |a| ==> CountOccurrences(a, a[k]) <= maxCount
  {
    var count := CountOccurrences(a, a[i]);
    if count == maxCount {
      biggest := biggest[a[i] := maxCount];
    }
    i := i + 1;
  }
}
// </vc-code>
