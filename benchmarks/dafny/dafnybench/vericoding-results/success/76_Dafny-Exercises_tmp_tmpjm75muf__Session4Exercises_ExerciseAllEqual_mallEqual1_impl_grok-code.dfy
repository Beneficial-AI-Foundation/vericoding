predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
if v.Length == 0 {
  return true;
} else {
  var first := v[0];
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] == first
  {
    if v[i] != first {
      return false;
    }
    i := i + 1;
  }
  return true;
}
}
// </vc-code>

