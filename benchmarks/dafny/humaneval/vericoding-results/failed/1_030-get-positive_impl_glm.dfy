// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added predicate to check if an element is in a sequence */
predicate InSeq(x: int, s: seq<int>) {
    exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)

    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant using InSeq helper */
{
    var res := [];
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant |res| <= i
        invariant forall j : int :: 0 <= j < |res| ==> res[j] > 0
        invariant forall j : int :: 0 <= j < i ==> (l[j] > 0 ==> InSeq(l[j], res))
        invariant forall j : int :: 0 <= j < |res| ==> exists k : int :: 0 <= k < i && l[k] == res[j]
    {
        if l[i] > 0 {
            res := res + [l[i]];
        }
        i := i + 1;
    }
    result := res;
}
// </vc-code>
