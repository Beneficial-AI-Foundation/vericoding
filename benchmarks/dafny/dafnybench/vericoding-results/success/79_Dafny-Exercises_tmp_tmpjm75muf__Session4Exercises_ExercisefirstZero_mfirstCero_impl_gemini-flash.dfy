

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0
// </vc-spec>
// <vc-code>
{
    var i_idx := 0;
    while i_idx < v.Length
        invariant 0 <= i_idx <= v.Length
        invariant forall j :: 0 <= j < i_idx ==> v[j] != 0
    {
        if v[i_idx] == 0 {
            return i_idx;
        }
        i_idx := i_idx + 1;
    }
    return i_idx;
}
// </vc-code>

