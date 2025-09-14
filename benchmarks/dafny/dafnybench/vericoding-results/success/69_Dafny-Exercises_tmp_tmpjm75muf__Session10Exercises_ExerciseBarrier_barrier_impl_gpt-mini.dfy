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
lemma RightWit(argMax:int, witnessL:int, v:array<int>, p:int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires 0 <= argMax <= p
  requires p < witnessL < v.Length
  requires v[argMax] >= v[witnessL]
  ensures exists k,l :: 0 <= k <= p && p < l < v.Length && !(v[k] < v[l])
{
  // Provide explicit witness (argMax, witnessL)
  assert 0 <= argMax <= p && p < witnessL < v.Length && v[argMax] >= v[witnessL];
  assert 0 <= argMax <= p && p < witnessL < v.Length && !(v[argMax] < v[witnessL]);
  assert exists k,l :: 0 <= k <= p && p < l < v.Length && !(v[k] < v[l]);
}

lemma GoodCase(maxLeft:int, v:array<int>, p:int)
  requires v.Length > 0
  requires 0 <= p < v.Length
  requires forall k :: 0 <= k <= p ==> v[k] <= maxLeft
  requires forall l :: p < l < v.Length ==> maxLeft < v[l]
  ensures forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
{
  // For arbitrary k,l satisfying the bounds we have v[k] <= maxLeft < v[l], so v[k] < v[l].
  assert forall k,l :: 0 <= k <= p && p < l < v.Length ==>
    (v[k] <= maxLeft && maxLeft < v[l] ==> v[k] < v[l]);
  // From the requires, for such k,l the antecedent holds, hence the implication gives the result.
  assert forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l];
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
  var n := v.Length;
  if p == n - 1 {
    b := true;
    return;
  }

  var maxLeft := v[0];
  var argMax := 0;
  var i := 1;
  while i <= p
    invariant 1 <= i <= p + 1
    invariant 0 <= argMax < v.Length
    invariant forall k :: 0 <= k < i ==> v[k] <= maxLeft
    invariant 0 <= argMax < i && v[argMax] == maxLeft
  {
    if v[i] > maxLeft {
      maxLeft := v[i];
      argMax := i;
    }
    i := i + 1;
  }

  var j := p + 1;
  var found := false;
  var witnessL := -1;
  while j < n
    invariant p + 1 <= j <= n
    invariant 0 <= argMax <= p
    invariant (found ==> (0 <= witnessL < n && v[argMax] >= v[witnessL]))
    invariant (found ==> p < witnessL < j)
    invariant (!found ==> forall l :: p + 1 <= l < j ==> maxLeft < v[l])
  {
    if v[j] <= maxLeft {
      found := true;
      witnessL := j;
    }
    j := j + 1;
  }

  if found {
    RightWit(argMax, witnessL, v, p);
    b := false;
  } else {
    GoodCase(maxLeft, v, p);
    b := true;
  }
}
// </vc-code>

