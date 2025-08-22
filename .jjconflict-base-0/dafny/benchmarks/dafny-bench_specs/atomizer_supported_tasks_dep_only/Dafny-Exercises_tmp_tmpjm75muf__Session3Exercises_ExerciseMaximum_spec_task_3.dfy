//Algorithm 1: From left to right return the first
//ATOM_PLACEHOLDER_mmaximum1

//Algorithm 2: From right to left return the last
//ATOM_PLACEHOLDER_mmaximum2


// SPEC 


method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right
{
}


//ATOM_PLACEHOLDER_mlastMaximum

//Algorithm : from left to right
//Algorithm : from right to left

//ATOM_PLACEHOLDER_mmaxvalue1

//ATOM_PLACEHOLDER_mmaxvalue2

