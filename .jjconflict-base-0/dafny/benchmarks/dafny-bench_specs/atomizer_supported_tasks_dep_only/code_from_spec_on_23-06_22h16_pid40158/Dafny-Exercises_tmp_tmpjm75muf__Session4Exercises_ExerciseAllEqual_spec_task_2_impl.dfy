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



//ATOM_PLACEHOLDER_equivalenceContiguous



//ATOM_PLACEHOLDER_mallEqual1

// IMPL 
method mallEqual2(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
{
    if v.Length == 0 {
        b := true;
        return;
    }
    
    var i := 1;
    while i < v.Length
        invariant 1 <= i <= v.Length
        invariant forall k :: 0 <= k < i ==> v[k] == v[0]
    {
        if v[i] != v[0] {
            b := false;
            return;
        }
        i := i + 1;
    }
    b := true;
}


//ATOM_PLACEHOLDER_mallEqual3


//ATOM_PLACEHOLDER_mallEqual4


//ATOM_PLACEHOLDER_mallEqual5