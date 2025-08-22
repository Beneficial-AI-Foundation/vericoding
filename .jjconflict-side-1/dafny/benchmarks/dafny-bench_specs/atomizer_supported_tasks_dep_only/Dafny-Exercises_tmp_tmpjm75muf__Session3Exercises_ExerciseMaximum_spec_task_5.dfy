//Algorithm 1: From left to right return the first
// SPEC 
//Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
}


//Algorithm 2: From right to left return the last
//ATOM_PLACEHOLDER_mmaximum2


//ATOM_PLACEHOLDER_mfirstMaximum

//ATOM_PLACEHOLDER_mlastMaximum

//Algorithm : from left to right
//Algorithm : from right to left

// SPEC 

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
{
}


//ATOM_PLACEHOLDER_mmaxvalue2

