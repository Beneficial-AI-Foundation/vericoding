// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function identity_seq(s: seq<int>): seq<int> { s }
lemma IdentityPreservesLength(s: seq<int>) ensures |s| == |identity_seq(s)| { }
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)

    ensures |s| == |strange|
// </vc-spec>
// <vc-code>
{
  strange := s;
}
// </vc-code>
