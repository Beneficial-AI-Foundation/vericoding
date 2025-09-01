

// <vc-helpers>
lemma SequenceConcatLemma(s: seq<int>, x: int, j: int)
    requires 0 <= j < |s|
    ensures (s + [x])[j] == s[j]
{
}
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := [];
    var index := 0;
    while index < |l|
        invariant |result| == index
        invariant forall j :: 0 <= j < index ==> result[j] == l[j] + 1
    {
        result := result + [l[index] + 1];
        index := index + 1;
        if index < |l| {
            var k :| 0 <= k < index;
            SequenceConcatLemma(result, l[index] + 1, k);
        }
    }
}
// </vc-code>

