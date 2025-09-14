predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
lemma AllEqualLemma(s: seq<int>)
  ensures allEqual(s) <==> (forall i :: 0 <= i < |s| ==> s[i] == s[0])
{
  if allEqual(s) {
    // If all are equal, then each element equals the first
    assert forall i :: 0 <= i < |s| ==> s[i] == s[0];
  }
  if (forall i :: 0 <= i < |s| ==> s[i] == s[0]) {
    // If each equals the first, then all are equal
    assert forall i,j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j];
  }
}
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length == 0 {
    b := true;
    return;
  }
  
  var first := v[0];
  var i := 0;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] == first
  {
    if v[i] != first {
      b := false;
      return;
    }
    i := i + 1;
  }
  
  b := true;
}
// </vc-code>

