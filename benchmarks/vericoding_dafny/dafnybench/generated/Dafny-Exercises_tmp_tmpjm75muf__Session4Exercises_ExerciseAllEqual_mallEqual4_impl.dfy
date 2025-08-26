predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
// <vc-spec>
lemma equivalenceNoOrder(s:seq<int>)
ensures allEqual(s) <==> forall i,j::0<=i<=j<|s| ==> s[i]==s[j]
{}

//All equal to first
lemma equivalenceEqualtoFirst(s:seq<int>)
requires s!=[]
ensures allEqual(s) <==> (forall i::0<=i<|s| ==> s[0]==s[i])
{}



lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
ensures (allEqual(s) <== forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
{
  assert allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1];

  if(|s|==0 || |s|==1){

  }
  else{
    calc {
      forall i::0<=i<|s|-1 ==> s[i]==s[i+1];
      ==>
      {
        equivalenceContiguous(s[..|s|-1]);
        assert s[|s|-2] == s[|s|-1];
      }
      allEqual(s);
    }
  }

}

// <vc-helpers>
// </vc-helpers>

method mallEqual4(v:array<int>) returns (b:bool)
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
    invariant forall k :: 0 <= k < i ==> v[0] == v[k]
  {
    if v[0] != v[i] {
      return false;
    }
    i := i + 1;
  }
  
  equivalenceEqualtoFirst(v[0..v.Length]);
  return true;
}
// </vc-code>