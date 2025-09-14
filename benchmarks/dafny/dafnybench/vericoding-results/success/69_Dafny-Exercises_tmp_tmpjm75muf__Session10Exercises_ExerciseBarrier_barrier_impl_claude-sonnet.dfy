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
  requires forall j :: 0 <= j <= p ==> maxLeft >= v[j]
  requires exists j :: 0 <= j <= p && maxLeft == v[j]
  ensures forall k :: 0 <= k <= p ==> maxLeft >= v[k]
{
}

lemma MinRightLemma(v: array<int>, p: int, minRight: int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires p + 1 < v.Length
  requires forall j :: p + 1 <= j < v.Length ==> minRight <= v[j]
  requires exists j :: p + 1 <= j < v.Length && minRight == v[j]
  ensures forall l :: p < l < v.Length ==> minRight <= v[l]
{
}

lemma BarrierCorrectness(v: array<int>, p: int, maxLeft: int, minRight: int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires forall k :: 0 <= k <= p ==> maxLeft >= v[k]
  requires p + 1 < v.Length ==> forall l :: p < l < v.Length ==> minRight <= v[l]
  requires p + 1 < v.Length ==> maxLeft < minRight
  ensures p + 1 >= v.Length || forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
{
  if p + 1 < v.Length {
    forall k,l | 0 <= k <= p && p < l < v.Length
      ensures v[k] < v[l]
    {
      assert maxLeft >= v[k];
      assert minRight <= v[l];
      assert maxLeft < minRight;
    }
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
  if p + 1 >= v.Length {
    b := true;
    return;
  }
  
  var maxLeft := v[0];
  var i := 1;
  while i <= p
    invariant 1 <= i <= p + 1
    invariant forall j :: 0 <= j < i && j <= p ==> maxLeft >= v[j]
    invariant exists j :: 0 <= j < i && j <= p && maxLeft == v[j]
  {
    if v[i] > maxLeft {
      maxLeft := v[i];
    }
    i := i + 1;
  }
  
  MaxLeftLemma(v, p, maxLeft);
  
  var minRight := v[p + 1];
  i := p + 2;
  while i < v.Length
    invariant p + 2 <= i <= v.Length
    invariant forall j :: p + 1 <= j < i ==> minRight <= v[j]
    invariant exists j :: p + 1 <= j < i && minRight == v[j]
  {
    if v[i] < minRight {
      minRight := v[i];
    }
    i := i + 1;
  }
  
  MinRightLemma(v, p, minRight);
  
  b := maxLeft < minRight;
  
  if b {
    BarrierCorrectness(v, p, maxLeft, minRight);
  }
}
// </vc-code>

