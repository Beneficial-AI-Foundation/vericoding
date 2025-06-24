//ATOM_PLACEHOLDER_LinearSearch

//ATOM_PLACEHOLDER_LinearSearch1


//ATOM_PLACEHOLDER_LinearSearch2

// SPEC 

method LinearSearch3<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
    requires |s1| <= data.Length
    requires forall i:: 0<= i <|s1| ==> s1[i] == data[data.Length -1-i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element && |s1| != 0
   // ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
}


