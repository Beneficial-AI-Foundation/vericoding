// ATOM 
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }

//{forall i,j::0<=i<=j<|s| ==> s[i]==s[j] }
//{forall i::0<i<|s| ==> s[i-1]==s[i]} 
//{forall i::0<=i<|s|-1 ==> s[i]==s[i+1]}


//Ordered indexes
//ATOM_PLACEHOLDER_equivalenceNoOrder

//All equal to first
//ATOM_PLACEHOLDER_equivalenceEqualtoFirst



// ATOM 



lemma equivalenceContiguous(s:seq<int>)
ensures (allEqual(s) ==> forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
ensures (allEqual(s) <== forall i::0<=i<|s|-1 ==> s[i]==s[i+1])
{
  
  if(|s|==0 || |s|==1){

  }
  else{
    calc {
      forall i::0<=i<|s|-1 ==> s[i]==s[i+1];
      ==>
      {
        equivalenceContiguous(s[..|s|-1]);
      }
      allEqual(s);
    }
  }
  
}




//ATOM_PLACEHOLDER_mallEqual1

//ATOM_PLACEHOLDER_mallEqual2



// IMPL mallEqual3

method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
  if v.Length <= 1 {
    /* code modified by LLM (iteration 1): simplified proof for small arrays */
    b := true;
    return;
  }
  
  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] == v[0]
  {
    if v[i] != v[0] {
      /* code modified by LLM (iteration 1): added proof that allEqual is false when elements differ */
      assert v[i] != v[0];
      assert v[0..v.Length][i] == v[i];
      assert v[0..v.Length][0] == v[0];
      assert !allEqual(v[0..v.Length]);
      b := false;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added proof that allEqual holds when all elements equal v[0] */
  assert forall k :: 0 <= k < v.Length ==> v[k] == v[0];
  assert forall x, y :: 0 <= x < v.Length && 0 <= y < v.Length ==> 
    v[0..v.Length][x] == v[x] == v[0] == v[y] == v[0..v.Length][y];
  assert allEqual(v[0..v.Length]);
  b := true;
}


//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5