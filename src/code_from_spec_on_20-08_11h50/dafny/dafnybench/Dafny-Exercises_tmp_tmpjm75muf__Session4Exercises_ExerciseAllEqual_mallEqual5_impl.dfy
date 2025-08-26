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

predicate allEqual(s: seq<int>) {
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
}

method mallEqual5(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length == 0 {
    b := true;
    return;
  }
  
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[0] == v[j]
  {
    if v[0] != v[i] {
      b := false;
      assert !allEqual(v[0..v.Length]) by {
        assert v[0] != v[i];
        assert 0 < |v[0..v.Length]| && i < |v[0..v.Length]|;
        assert v[0..v.Length][0] == v[0];
        assert v[0..v.Length][i] == v[i];
        assert v[0..v.Length][0] != v[0..v.Length][i];
      }
      return;
    }
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < v.Length ==> v[0] == v[j];
  assert forall j :: 0 <= j < |v[0..v.Length]| ==> v[0..v.Length][0] == v[0..v.Length][j] by {
    forall j | 0 <= j < |v[0..v.Length]| ensures v[0..v.Length][0] == v[0..v.Length][j] {
      assert v[0..v.Length][0] == v[0];
      assert v[0..v.Length][j] == v[j];
      assert v[0] == v[j];
    }
  }
  equivalenceEqualtoFirst(v[0..v.Length]);
  assert allEqual(v[0..v.Length]);
  b := true;
}