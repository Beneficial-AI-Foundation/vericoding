// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ExtractRearChars(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ExtractRearCharsImpl(l: seq<string>) returns (r: seq<char>)
    requires forall i :: 0 <= i < |l| ==> |l[i]| > 0
    ensures |r| == |l|
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i][|l[i]| - 1]
{
    r := [];
    for i := 0 to |l|
        invariant |r| == i
        invariant forall k :: 0 <= k < i ==> r[k] == l[k][|l[k]| - 1]
    {
        r := r + [l[i][|l[i]| - 1]];
    }
}
// </vc-code>
