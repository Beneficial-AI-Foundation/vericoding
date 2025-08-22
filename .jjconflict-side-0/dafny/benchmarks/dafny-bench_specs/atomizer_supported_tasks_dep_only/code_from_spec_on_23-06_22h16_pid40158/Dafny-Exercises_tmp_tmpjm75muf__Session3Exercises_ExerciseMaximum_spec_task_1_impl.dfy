//IMPL Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    i := 0;
    var j := 1;
    
    while j < v.Length
        invariant 0 <= i < v.Length
        invariant 1 <= j <= v.Length
        invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    {
        if v[j] > v[i] {
            i := j;
        }
        j := j + 1;
    }
}

//Algorithm 2: From right to left return the last
//ATOM_PLACEHOLDER_mmaximum2

//ATOM_PLACEHOLDER_mfirstMaximum

//ATOM_PLACEHOLDER_mlastMaximum

//Algorithm : from left to right
//Algorithm : from right to left

//ATOM_PLACEHOLDER_mmaxvalue1

//ATOM_PLACEHOLDER_mmaxvalue2