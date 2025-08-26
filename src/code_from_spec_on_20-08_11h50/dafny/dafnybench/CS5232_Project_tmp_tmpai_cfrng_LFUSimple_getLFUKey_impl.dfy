class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; //key -> {value, freq}

// <vc-spec>
    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
      // reads this.freqMap.Values;
    {
      // general value check
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].1 >= 1)) && // frequency should always larger than 0
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].0 >= 0)) // only allow positive values
    }

// <vc-helpers>
function MinInSet(s: set<int>): int
  requires s != {}
{
  var x :| x in s && forall y :: y in s ==> x <= y;
  x
}

function SetToSeq(s: set<int>): seq<int>
{
  if s == {} then []
  else 
    var x := MinInSet(s);
    [x] + SetToSeq(s - {x})
}

lemma SetToSeqContainsAll(s: set<int>)
  ensures forall x :: x in s <==> x in SetToSeq(s)
{
  if s == {} {
    // base case: empty set
  } else {
    var x := MinInSet(s);
    var rest := s - {x};
    SetToSeqContainsAll(rest);
    assert SetToSeq(s) == [x] + SetToSeq(rest);
  }
}

lemma SetToSeqLength(s: set<int>)
  ensures |SetToSeq(s)| == |s|
{
  if s == {} {
    // base case
  } else {
    var x := MinInSet(s);
    var rest := s - {x};
    SetToSeqLength(rest);
  }
}
// </vc-helpers>

method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap.Keys ==> cacheMap[lfuKey].1 <= cacheMap[k].1;
// </vc-spec>
// <vc-code>
{
  var keys := cacheMap.Keys;
  var keysSeq := SetToSeq(keys);
  
  // Establish key properties about the sequence
  SetToSeqContainsAll(keys);
  SetToSeqLength(keys);
  
  assert |keysSeq| == |keys|;
  assert |keys| == |cacheMap|;
  assert |cacheMap| > 0;
  assert |keysSeq| > 0;
  
  var minKey := keysSeq[0];
  assert minKey in keysSeq;
  assert minKey in keys;
  assert minKey in cacheMap;
  
  var minFreq := cacheMap[minKey].1;
  var i := 1;
  
  while i < |keysSeq|
    invariant 0 <= i <= |keysSeq|
    invariant minKey in keys
    invariant minKey in cacheMap
    invariant minFreq == cacheMap[minKey].1
    invariant forall j :: 0 <= j < i ==> minFreq <= cacheMap[keysSeq[j]].1
    invariant forall j :: 0 <= j < |keysSeq| ==> keysSeq[j] in cacheMap
  {
    var key := keysSeq[i];
    assert key in keysSeq;
    assert key in keys;
    assert key in cacheMap;
    
    if cacheMap[key].1 < minFreq {
      minKey := key;
      minFreq := cacheMap[key].1;
    }
    i := i + 1;
  }
  
  // Prove the final postcondition
  assert forall j :: 0 <= j < |keysSeq| ==> minFreq <= cacheMap[keysSeq[j]].1;
  assert forall k :: k in keys <==> k in keysSeq;
  assert forall k :: k in cacheMap.Keys ==> k in keys;
  
  lfuKey := minKey;
}
// </vc-code>

}