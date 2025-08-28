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
lemma MaxLeftLemma(v: array<int>, p: int, maxLeft: int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires maxLeft == MaxInRange(v, 0, p)
  ensures forall k :: 0 <= k <= p ==> v[k] <= maxLeft
{
  MaxInRangeSound(v, 0, p);
}

lemma MinRightLemma(v: array<int>, p: int, minRight: int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires p + 1 < v.Length
  requires minRight == MinInRange(v, p + 1, v.Length - 1)
  ensures forall l :: p < l < v.Length ==> minRight <= v[l]
{
  MinInRangeSound(v, p + 1, v.Length - 1);
}

lemma MaxInRangeSound(v: array<int>, start: int, end: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures forall k :: start <= k <= end ==> v[k] <= MaxInRange(v, start, end)
  decreases end - start
{
  if start == end {
  } else {
    MaxInRangeSound(v, start + 1, end);
  }
}

lemma MinInRangeSound(v: array<int>, start: int, end: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures forall k :: start <= k <= end ==> MinInRange(v, start, end) <= v[k]
  decreases end - start
{
  if start == end {
  } else {
    MinInRangeSound(v, start + 1, end);
  }
}

function MaxInRange(v: array<int>, start: int, end: int): int
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  reads v
  decreases end - start
{
  if start == end then v[start]
  else if v[start] > MaxInRange(v, start + 1, end) then v[start]
  else MaxInRange(v, start + 1, end)
}

function MinInRange(v: array<int>, start: int, end: int): int
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  reads v
  decreases end - start
{
  if start == end then v[start]
  else if v[start] < MinInRange(v, start + 1, end) then v[start]
  else MinInRange(v, start + 1, end)
}

lemma FindMaxIndex(v: array<int>, start: int, end: int) returns (maxIdx: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures start <= maxIdx <= end
  ensures v[maxIdx] == MaxInRange(v, start, end)
  decreases end - start
{
  if start == end {
    maxIdx := start;
  } else {
    var restMaxIdx := FindMaxIndex(v, start + 1, end);
    if v[start] > v[restMaxIdx] {
      maxIdx := start;
    } else {
      maxIdx := restMaxIdx;
    }
  }
}

lemma FindMinIndex(v: array<int>, start: int, end: int) returns (minIdx: int)
  requires v.Length > 0
  requires 0 <= start <= end < v.Length
  ensures start <= minIdx <= end
  ensures v[minIdx] == MinInRange(v, start, end)
  decreases end - start
{
  if start == end {
    minIdx := start;
  } else {
    var restMinIdx := FindMinIndex(v, start + 1, end);
    if v[start] < v[restMinIdx] {
      minIdx := start;
    } else {
      minIdx := restMinIdx;
    }
  }
}

lemma BarrierCorrectness(v: array<int>, p: int, maxLeft: int, minRight: int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires p + 1 < v.Length
  requires forall k :: 0 <= k <= p ==> v[k] <= maxLeft
  requires forall l :: p < l < v.Length ==> minRight <= v[l]
  requires exists k :: 0 <= k <= p && v[k] == maxLeft
  requires exists l :: p < l < v.Length && v[l] == minRight
  ensures (maxLeft < minRight) == (forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l])
{
  if maxLeft < minRight {
    forall k, l | 0 <= k <= p && p < l < v.Length
      ensures v[k] < v[l]
    {
      assert v[k] <= maxLeft;
      assert minRight <= v[l];
      assert maxLeft < minRight;
    }
  } else {
    var maxIdx :| 0 <= maxIdx <= p && v[maxIdx] == maxLeft;
    var minIdx :| p < minIdx < v.Length && v[minIdx] == minRight;
    assert v[maxIdx] >= minRight;
    assert !(v[maxIdx] < v[minIdx]);
    assert !(forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method barrier(v:array<int>,p:int) returns (b:bool)
//Give the precondition
//Give the postcondition
//{Implement and verify}
requires v.Length > 0
requires 0<=p<v.Length
ensures b==forall k,l::0<=k<=p && p<l<v.Length ==> v[k]<v[l]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if p == v.Length - 1 {
    b := true;
    return;
  }
  
  var maxLeft := v[0];
  var i := 1;
  
  while i <= p
    invariant 1 <= i <= p + 1
    invariant forall k :: 0 <= k < i ==> v[k] <= maxLeft
    invariant exists k :: 0 <= k < i && v[k] == maxLeft
  {
    if v[i] > maxLeft {
      maxLeft := v[i];
    }
    i := i + 1;
  }
  
  assert forall k :: 0 <= k <= p ==> v[k] <= maxLeft;
  assert exists k :: 0 <= k <= p && v[k] == maxLeft;
  
  var minRight := v[p + 1];
  i := p + 2;
  
  while i < v.Length
    invariant p + 2 <= i <= v.Length
    invariant forall l :: p + 1 <= l < i ==> minRight <= v[l]
    invariant exists l :: p + 1 <= l < i && v[l] == minRight
  {
    if v[i] < minRight {
      minRight := v[i];
    }
    i := i + 1;
  }
  
  assert forall l :: p < l < v.Length ==> minRight <= v[l];
  assert exists l :: p < l < v.Length && v[l] == minRight;
  
  b := maxLeft < minRight;
  
  BarrierCorrectness(v, p, maxLeft, minRight);
}
// </vc-code>
