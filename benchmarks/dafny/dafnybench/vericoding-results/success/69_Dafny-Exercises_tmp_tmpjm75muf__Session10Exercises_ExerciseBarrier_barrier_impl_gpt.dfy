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
    b := forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l];
    return;
  }

  var maxL := v[0];
  var i := 1;
  while i <= p
    invariant 1 <= i <= p + 1
    invariant forall k :: 0 <= k < i ==> v[k] <= maxL
    decreases p - i + 1
  {
    if v[i] > maxL {
      maxL := v[i];
    }
    i := i + 1;
  }

  var minR := v[p + 1];
  var j := p + 2;
  while j < v.Length
    invariant p + 2 <= j <= v.Length
    invariant forall l :: p < l < j ==> minR <= v[l]
    decreases v.Length - j
  {
    if v[j] < minR {
      minR := v[j];
    }
    j := j + 1;
  }

  b := forall k,l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l];
}
// </vc-code>

