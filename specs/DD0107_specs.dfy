// <vc-preamble>
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
    var i:=0; b:=true;
    while(i<v.Length && b)
        decreases v.Length - i 
        invariant 0 <= i <= v.Length
        invariant b==positive(v[0..i])
        invariant !b ==> !positive(v[0..v.Length])
    {
        b:=v[i]>=0;
        i:=i+1;
    }
}
// </vc-code>
