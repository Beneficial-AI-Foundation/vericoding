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



// SPEC 



method mallEqual3(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
}



//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5









