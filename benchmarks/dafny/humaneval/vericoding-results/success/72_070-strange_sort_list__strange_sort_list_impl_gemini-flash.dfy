// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
