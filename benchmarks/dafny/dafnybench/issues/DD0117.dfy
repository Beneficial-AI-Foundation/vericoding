// <vc-preamble>
//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last
method mmaximum2(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=v.Length-2; i:=v.Length - 1;
    while(j>=0)
        decreases j
        invariant 0<=i<v.Length
        invariant -1<=j<v.Length-1
        invariant forall k :: v.Length>k>j ==> v[k]<=v[i]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j-1;
    }
}




//Algorithm : from left to right
//Algorithm : from right to left
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mmaxvalue2(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
// </vc-spec>
// <vc-code>
{
    var i:=mmaximum2(v);
    m:=v[i];
}
// </vc-code>
