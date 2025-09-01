

// <vc-helpers>
function safeIncr(s: seq<int>, i: int): int
  requires 0 <= i < |s|
{
  s[i] + 1
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
    result := seq(|l|, i => safeIncr(l, i));
}
// </vc-code>

