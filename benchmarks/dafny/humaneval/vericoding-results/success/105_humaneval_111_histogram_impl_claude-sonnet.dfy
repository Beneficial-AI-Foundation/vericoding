// <vc-preamble>
type BiggestMap = map<int, int>
// </vc-preamble>

// <vc-helpers>
function countOccurrences(a: seq<int>, val: int): int
{
  |set j | 0 <= j < |a| && a[j] == val|
}

/* helper modified by LLM (iteration 3): converted function to method to fix compilation error */
method getMaxCount(a: seq<int>) returns (maxCount: int)
  requires |a| > 0
  ensures forall j :: 0 <= j < |a| ==> countOccurrences(a, a[j]) <= maxCount
  ensures exists j :: 0 <= j < |a| && countOccurrences(a, a[j]) == maxCount
{
  var i := 0;
  maxCount := countOccurrences(a, a[0]);
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> countOccurrences(a, a[j]) <= maxCount
    invariant exists j :: 0 <= j < |a| && countOccurrences(a, a[j]) == maxCount
  {
    var count := countOccurrences(a, a[i]);
    if count > maxCount {
      maxCount := count;
    }
    i := i + 1;
  }
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
/* code modified by LLM (iteration 3): fixed method call to getMaxCount */
{
  if |a| == 0 {
    biggest := map[];
    return;
  }
  
  var maxCount := getMaxCount(a);
  biggest := map[];
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: k in biggest ==> biggest[k] == maxCount
    invariant forall j :: 0 <= j < i && countOccurrences(a, a[j]) == maxCount ==> a[j] in biggest
    invariant forall k :: k in biggest ==> countOccurrences(a, k) == maxCount
  {
    var count := countOccurrences(a, a[i]);
    if count == maxCount {
      biggest := biggest[a[i] := maxCount];
    }
    i := i + 1;
  }
  
  // Help prove the postconditions
  assert forall k :: k in biggest ==> countOccurrences(a, k) == maxCount;
  assert forall j :: 0 <= j < |a| && countOccurrences(a, a[j]) == maxCount ==> a[j] in biggest;
}
// </vc-code>
