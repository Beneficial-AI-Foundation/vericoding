

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method incr_list(l: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == l[i] + 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
result := seq(|l|, i => l[i] + 1);
// </vc-code>

