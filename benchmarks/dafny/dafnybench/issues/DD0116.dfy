// <vc-preamble>
//Algorithm 1: From left to right return the first
method mmaximum1(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
{
    var j:=1; i:=0;
    while(j<v.Length)
        decreases v.Length - j
        invariant 0<=j<=v.Length
        invariant 0<=i<j
        invariant forall k:: 0<=k<j ==> v[i] >= v[k]
    {
        if(v[j] > v[i]){i:=j;}
        j:=j+1;
    }
}

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mmaxvalue1(v:array<int>) returns (m:int)
requires v.Length>0
ensures m in v[..]
ensures forall k::0<=k<v.Length ==> m>=v[k]
// </vc-spec>
// <vc-code>
{
    var i:=mmaximum1(v);
    m:=v[i];
}
// </vc-code>
