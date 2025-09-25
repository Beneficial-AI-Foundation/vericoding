// <vc-preamble>
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
    var i:=v.Length-1;
    while(i>=0 && v[i]>=0)
        decreases i
        invariant -1 <= i < v.Length
        invariant positive(v[i+1..])
    {
        i:=i-1;
    }
    b:= i==-1;
}
// </vc-code>
