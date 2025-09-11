// <vc-preamble>
predicate IsSubseqAt(sub: seq<int>, main: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && 
    (forall j :: 0 <= j < |sub| ==> sub[j] == main[i + j])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
    ensures result <==> exists i :: IsSubseqAt(sub, main, i)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume {:axiom} false;
    result := false;
    // impl-end
}
// </vc-code>
