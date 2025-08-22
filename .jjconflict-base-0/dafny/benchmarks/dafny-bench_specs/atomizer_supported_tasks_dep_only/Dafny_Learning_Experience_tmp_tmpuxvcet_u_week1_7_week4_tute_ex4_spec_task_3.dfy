//ATOM_PLACEHOLDER_LinearSearch

//ATOM_PLACEHOLDER_LinearSearch1


// SPEC 


method LinearSearch2<T(==)>(data: array<T>, Element:T, s1:seq<T>) returns (position:int)
    requires |s1| <= data.Length
    requires forall i:: 0<= i <|s1| ==> s1[i] == data[i]
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i::0 <=i < |s1| && s1[i] == Element
    ensures position == -1 ==> forall i :: 0 <= i < |s1| ==> s1[i] != Element
{
}


//ATOM_PLACEHOLDER_LinearSearch3

