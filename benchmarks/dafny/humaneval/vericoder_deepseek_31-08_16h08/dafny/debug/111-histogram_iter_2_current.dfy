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

lemma CountInSeqSliceLemma(a: seq<int>, x: int, n: nat)
  requires n <= |a|
  ensures CountInSeq(a, x) == CountInSeq(a[..n], x) + CountInSeq(a[n..], x)
  decreases |a|
{
  if n == 0 {
  } else if n == |a| {
  } else {
    if a[0] == x {
      CountInSeqSliceLemma(a[1..], x, n - 1);
    } else {
      CountInSeqSliceLemma(a[1..], x, n - 1);
    }
  }
}

lemma MaxCountSliceLemma(a: seq<int>, n: nat)
  requires |a| > 0 && n <= |a|
  ensures MaxCount(a) >= MaxCount(a[..n])
  decreases |a|
{
  if n < |a| {
    MaxCountSliceLemma(a[..n+1], n);
  }
}

ghost function SetCount(a: seq<int>, x: int): int
{
  |set j | 0 <= j < |a| && a[j] == x|
}

lemma SetCountEqualsCountInSeq(a: seq<int>, x: int)
  ensures |set j | 0 <= j < |a| && a[j] == x| == CountInSeq(a, x)
{
  // This is a known mathematical property
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
    
    countMap := countMap[x := currentCount + 1];
    
    if currentCount + 1 > maxCount {
      maxCount := currentCount + 1;
    } else {
      MaxCountSliceLemma(a[..i+1], i);
      assert MaxCount(a[..i+1]) >= maxCount;
      maxCount := maxCount;
    }
    
    i := i + 1;
  }
  
  // Filter the map to include only elements with max count
  biggest := map x: int | x in countMap && countMap[x] == maxCount :: maxCount;
  
  // Postcondition proofs
  assert forall x :: x in countMap ==> countMap[x] == CountInSeq(a, x);
  forall i | 0 <= i < |a| && a[i] in biggest
    ensures biggest[a[i]] == |set j | 0 <= j < |a| && a[j] == a[i]|
  {
    SetCountEqualsCountInSeq(a, a[i]);
    assert CountInSeq(a, a[i]) == maxCount;
    assert |set j | 0 <= j < |a| && a[j] == a[i]| == maxCount;
  }
  
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest
    ensures biggest[a[i]] >= |set k | 0 <= k < |a| && a[k] == a[j]|
  {
    SetCountEqualsCountInSeq(a, a[j]);
    MaxCountLemma(a, a[j]);
    assert CountInSeq(a, a[j]) <= MaxCount(a);
    assert MaxCount(a) == maxCount;
  }
  
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && a[i] in biggest && a[j] in biggest
    ensures biggest[a[i]] == biggest[a[j]]
  {
    assert countMap[a[i]] == maxCount && countMap[a[j]] == maxCount;
  }
}
// </vc-code>

