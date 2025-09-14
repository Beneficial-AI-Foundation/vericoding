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
lemma lemma_max_prefix(v: array<int>, p: int, max_prefix: int)
  requires 0 <= p < v.Length
  requires forall i :: 0 <= i <= p ==> v[i] <= max_prefix
  requires exists i :: 0 <= i <= p && v[i] == max_prefix
  ensures forall k :: 0 <= k <= p ==> v[k] <= max_prefix
{
}

lemma lemma_min_suffix(v: array<int>, p: int, min_suffix: int)
  requires 0 <= p < v.Length - 1  // Add this to ensure p+1 < v.Length
  requires forall j :: p < j < v.Length ==> min_suffix <= v[j]
  requires exists j :: p < j < v.Length && v[j] == min_suffix
  ensures forall l :: p < l < v.Length ==> min_suffix <= v[l]
{
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
  var max_prefix := v[p];
  
  var i := 0;
  while i <= p
    invariant 0 <= i <= p+1
    invariant forall k :: 0 <= k < i ==> v[k] <= max_prefix
    invariant exists k :: 0 <= k <= p && v[k] == max_prefix
  {
    if v[i] > max_prefix {
      max_prefix := v[i];
    }
    i := i + 1;
  }
  
  // Handle case when p is the last element
  if p == v.Length - 1 {
    b := true;
    return;
  }
  
  var min_suffix := v[p+1];
  var j := p+1;
  while j < v.Length
    invariant p+1 <= j <= v.Length
    invariant forall l :: p < l < j ==> min_suffix <= v[l]
    invariant exists l :: p < l < v.Length && v[l] == min_suffix
  {
    if v[j] < min_suffix {
      min_suffix := v[j];
    }
    j := j + 1;
  }
  
  b := max_prefix < min_suffix;
}
// </vc-code>

