predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
lemma allEqualImpliesEqualToFirst(s: seq<int>, i: int)
  requires allEqual(s)
  requires 0 <= i < |s|
  requires |s| > 0
  ensures s[i] == s[0]
{
}

lemma equalToFirstImpliesAllEqual(s: seq<int>)
  requires |s| > 0
  requires forall k :: 0 <= k < |s| ==> s[k] == s[0]
  ensures allEqual(s)
{
}
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    return true;
  }
  
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] == v[0]
  {
    if v[i] != v[0] {
      return false;
    }
    i := i + 1;
  }
  
  equalToFirstImpliesAllEqual(v[0..v.Length]);
  return true;
}
// </vc-code>

