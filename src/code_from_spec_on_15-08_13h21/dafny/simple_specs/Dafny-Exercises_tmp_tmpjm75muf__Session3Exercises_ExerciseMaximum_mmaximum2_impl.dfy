//IMPL 

//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    i := v.Length - 1;
    var j := v.Length - 2;
    
    while j >= 0
        invariant -1 <= j < v.Length - 1
        invariant 0 <= i < v.Length
        invariant forall k :: j + 1 <= k < v.Length ==> v[i] >= v[k]
    {
        if v[j] >= v[i] {
            i := j;
        }
        j := j - 1;
    }
}