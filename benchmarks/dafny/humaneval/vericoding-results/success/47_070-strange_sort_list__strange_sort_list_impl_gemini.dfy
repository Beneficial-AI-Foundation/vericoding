// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function reverse(s: seq<int>): seq<int>
  ensures |reverse(s)| == |s|
{
  if s == [] then [] else reverse(s[1..]) + [s[0]]
}
// </vc-helpers>

// <vc-spec>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)

    ensures |s| == |strange|
// </vc-spec>
// <vc-code>
{
  strange := reverse(s);
}
// </vc-code>
