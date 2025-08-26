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
    b := true;
    return;
  }
  
  // Find maximum in left part (0 to p inclusive)
  var max_left := v[0];
  var i := 1;
  while i <= p
    invariant 1 <= i <= p + 1
    invariant forall j :: 0 <= j < i ==> v[j] <= max_left
    invariant exists j :: 0 <= j < i && v[j] == max_left
  {
    if v[i] > max_left {
      max_left := v[i];
    }
    i := i + 1;
  }
  
  // Find minimum in right part (p+1 to v.Length-1)
  var min_right := v[p+1];
  i := p + 2;
  while i < v.Length
    invariant p + 2 <= i <= v.Length
    invariant forall j :: p + 1 <= j < i ==> v[j] >= min_right
    invariant exists j :: p + 1 <= j < i && v[j] == min_right
  {
    if v[i] < min_right {
      min_right := v[i];
    }
    i := i + 1;
  }
  
  b := max_left < min_right;
}
// </vc-code>