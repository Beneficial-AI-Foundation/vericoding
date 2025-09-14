//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 

//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method

// <vc-helpers>
lemma BarrierEquivalence(v: array<int>, p: int, maxLeft: int, minRight: int)
  requires v.Length > 0
  requires 0 <= p < v.Length - 1
  requires maxLeft == MaxInRange(v, 0, p)
  requires minRight == MinInRange(v, p+1, v.Length-1)
  ensures (maxLeft < minRight) <==> (forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l])
{
  if maxLeft < minRight {
    forall k, l | 0 <= k <= p && p < l < v.Length
      ensures v[k] < v[l]
    {
      MaxInRangeProperty(v, 0, p, k);
      assert v[k] <= maxLeft;
      MinInRangeProperty(v, p+1, v.Length-1, l);
      assert minRight <= v[l];
    }
  } else {
    var k, l := FindCounterExample(v, p, maxLeft, minRight);
    assert 0 <= k <= p && p < l < v.Length && v[k] >= v[l];
  }
}

function MaxInRange(v: array<int>, start: int, end: int): int
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  reads v
  decreases end - start
{
  if start == end then v[start]
  else 
    var rest := MaxInRange(v, start+1, end);
    if v[start] > rest then v[start] else rest
}

function MinInRange(v: array<int>, start: int, end: int): int
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  reads v
  decreases end - start
{
  if start == end then v[start]
  else
    var rest := MinInRange(v, start+1, end);
    if v[start] < rest then v[start] else rest
}

lemma MaxInRangeProperty(v: array<int>, start: int, end: int, i: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  requires start <= i <= end
  ensures v[i] <= MaxInRange(v, start, end)
  decreases end - start
{
  if start == end {
    assert v[i] == v[start] == MaxInRange(v, start, end);
  } else if i == start {
    var rest := MaxInRange(v, start+1, end);
    assert MaxInRange(v, start, end) == if v[start] > rest then v[start] else rest;
  } else {
    MaxInRangeProperty(v, start+1, end, i);
  }
}

lemma MinInRangeProperty(v: array<int>, start: int, end: int, i: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  requires start <= i <= end
  ensures v[i] >= MinInRange(v, start, end)
  decreases end - start
{
  if start == end {
    assert v[i] == v[start] == MinInRange(v, start, end);
  } else if i == start {
    var rest := MinInRange(v, start+1, end);
    assert MinInRange(v, start, end) == if v[start] < rest then v[start] else rest;
  } else {
    MinInRangeProperty(v, start+1, end, i);
  }
}

lemma FindCounterExample(v: array<int>, p: int, maxLeft: int, minRight: int) returns (k: int, l: int)
  requires v.Length > 0
  requires 0 <= p < v.Length - 1
  requires maxLeft == MaxInRange(v, 0, p)
  requires minRight == MinInRange(v, p+1, v.Length-1)
  requires maxLeft >= minRight
  ensures 0 <= k <= p && p < l < v.Length
  ensures v[k] >= v[l]
{
  k := FindMaxIndex(v, 0, p);
  l := FindMinIndex(v, p+1, v.Length-1);
  assert v[k] == maxLeft;
  assert v[l] == minRight;
}

lemma FindMaxIndex(v: array<int>, start: int, end: int) returns (idx: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures start <= idx <= end
  ensures v[idx] == MaxInRange(v, start, end)
  ensures forall i :: start <= i <= end ==> v[i] <= v[idx]
  decreases end - start
{
  if start == end {
    idx := start;
  } else {
    var restIdx := FindMaxIndex(v, start+1, end);
    if v[start] > v[restIdx] {
      idx := start;
    } else {
      idx := restIdx;
    }
  }
}

lemma FindMinIndex(v: array<int>, start: int, end: int) returns (idx: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures start <= idx <= end
  ensures v[idx] == MinInRange(v, start, end)
  ensures forall i :: start <= i <= end ==> v[i] >= v[idx]
  decreases end - start
{
  if start == end {
    idx := start;
  } else {
    var restIdx := FindMinIndex(v, start+1, end);
    if v[start] < v[restIdx] {
      idx := start;
    } else {
      idx := restIdx;
    }
  }
}

lemma MaxInRangeExtend(v: array<int>, start: int, end: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length - 1
  ensures MaxInRange(v, start, end+1) == if v[end+1] > MaxInRange(v, start, end) then v[end+1] else MaxInRange(v, start, end)
  decreases end - start
{
  if start == end {
    assert MaxInRange(v, start, end+1) == MaxInRange(v, start, end+1);
  } else {
    MaxInRangeExtend(v, start+1, end);
  }
}

lemma MinInRangeExtend(v: array<int>, start: int, end: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length - 1
  ensures MinInRange(v, start, end+1) == if v[end+1] < MinInRange(v, start, end) then v[end+1] else MinInRange(v, start, end)
  decreases end - start
{
  if start == end {
    assert MinInRange(v, start, end+1) == MinInRange(v, start, end+1);
  } else {
    MinInRangeExtend(v, start+1, end);
  }
}
// </vc-helpers>

// <vc-spec>
method barrier(v:array<int>,p:int) returns (b:bool)
//Give the precondition
//Give the postcondition
//{Implement and verify}
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
// </vc-spec>
// <vc-code>
{
  if p == v.Length - 1 {
    b := true;
  } else {
    var maxLeft := v[0];
    var i := 1;
    while i <= p
      invariant 1 <= i <= p + 1
      invariant maxLeft == MaxInRange(v, 0, i-1)
      invariant forall j :: 0 <= j < i ==> v[j] <= maxLeft
    {
      MaxInRangeExtend(v, 0, i-1);
      if v[i] > maxLeft {
        maxLeft := v[i];
      }
      i := i + 1;
    }
    assert maxLeft == MaxInRange(v, 0, p);

    var minRight := v[p+1];
    i := p + 2;
    while i < v.Length
      invariant p + 2 <= i <= v.Length
      invariant minRight == MinInRange(v, p+1, i-1)
      invariant forall j :: p+1 <= j < i ==> v[j] >= minRight
    {
      MinInRangeExtend(v, p+1, i-1);
      if v[i] < minRight {
        minRight := v[i];
      }
      i := i + 1;
    }
    assert minRight == MinInRange(v, p+1, v.Length-1);

    b := maxLeft < minRight;
    BarrierEquivalence(v, p, maxLeft, minRight);
  }
}
// </vc-code>

