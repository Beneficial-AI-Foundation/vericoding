//Algorithm 1: From left to right return the first
//ATOM_PLACEHOLDER_mmaximum1

//Algorithm 2: From right to left return the last
// SPEC 

//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
}



//ATOM_PLACEHOLDER_mfirstMaximum

//ATOM_PLACEHOLDER_mlastMaximum

//Algorithm : from left to right
//Algorithm : from right to left

//ATOM_PLACEHOLDER_mmaxvalue1

// SPEC 

method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
}


