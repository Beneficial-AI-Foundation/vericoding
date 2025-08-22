//IMPL 

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]
{
    i := 0;
    var j := 1;
    
    // Find the maximum value by scanning left to right
    // But keep updating i to get the rightmost occurrence
    while j < v.Length
        invariant 1 <= j <= v.Length
        invariant 0 <= i < j
        invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
        invariant forall k :: i < k < j ==> v[i] > v[k]
    {
        if v[j] >= v[i] {
            i := j;
        }
        j := j + 1;
    }
}