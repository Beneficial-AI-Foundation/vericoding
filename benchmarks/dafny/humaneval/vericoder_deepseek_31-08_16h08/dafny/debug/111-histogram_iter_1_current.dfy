type BiggestMap = map<int, int>

// <vc-helpers>
function max(a: int, b: int): int {
  if a > b then a else b
}

function CountInSeq(a: seq<int>, x: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == x then 1 else 0) + CountInSeq(a[1..], x)
}

lemma CountInSeqLemma(a: seq<int>, x: int, y: int)
  ensures x != y ==> CountInSeq(a, x) + CountInSeq(a, y) <= |a|
  decreases |a|
{
  if |a| > 0 {
    CountInSeqLemma(a[1..], x, y);
  }
}

function MaxCount(a: seq<int>): int
  decreases |a|
  requires |a| > 0
{
  if |a| == 1 then 1
  else max(CountInSeq(a, a[0]), MaxCount(a[1..]))
}

lemma MaxCountLemma(a: seq<int>, x: int)
  requires |a| > 0
  ensures CountInSeq(a, x) <= MaxCount(a)
  decreases |a|
{
  if |a| == 1 {
    // Trivial case
  } else {
    if a[0] == x {
      assert CountInSeq(a, x) == 1 + CountInSeq(a[1..], x);
      MaxCountLemma(a[1..], x);
    } else {
      MaxCountLemma(a[1..], x);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>) returns (biggest: BiggestMap)
  // post-conditions-start
  ensures forall i :: 0 <= i < |a| && a[i] in biggest ==>
    biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest ==>
    biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  ensures forall i, j :: 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest ==>
    biggest[a[i]] == biggest[a[j]]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var countMap := map[];
  var maxCount := 0;
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall x :: x in countMap ==> countMap[x] == CountInSeq(a[..i], x)
    invariant maxCount == (if i > 0 then MaxCount(a[..i]) else 0)
  {
    var x := a[i];
    var currentCount := CountInSeq(a[..i], x);
    
    if x in countMap {
      countMap := countMap[x := currentCount + 1];
    } else {
      countMap := countMap[x := currentCount + 1];
    }
    
    if currentCount + 1 > maxCount {
      maxCount := currentCount + 1;
    }
    
    i := i + 1;
  }
  
  // Filter the map to include only elements with max count
  biggest := map x: int | x in countMap && countMap[x] == maxCount :: countMap[x];
}
// </vc-code>

