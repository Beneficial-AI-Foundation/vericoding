predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes

//All equal to first

// <vc-helpers>
// Helper lemma to prove properties about allEqual predicate if needed
lemma AllEqualProperty(s: seq<int>)
  ensures allEqual(s) ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
{
  // This is directly from the definition, so no additional proof needed
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// </vc-spec>

// <vc-code>
method mallEqual(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  if v.Length == 0 {
    return true;
  }
  
  var first := v[0];
  var i := 0;
  b := true;
  
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant b ==> forall k :: 0 <= k < i ==> v[k] == first
  {
    if v[i] != first {
      b := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
