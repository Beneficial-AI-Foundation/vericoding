// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma PrefixTwiceId(a: seq<int>, n: int)
  requires 0 <= n <= |a|
  ensures a[0..n][..n] == a[0..n]
{ }
// </vc-helpers>

// <vc-spec>
method ReverseToK(list: array<int>, n: int) returns (reversed_list: seq<int>)
    requires
        list.Length > 0 &&
        0 < n < list.Length
    ensures
        reversed_list == list[0..n][..n] + list[n..list.Length]
// </vc-spec>
// <vc-code>
{
  reversed_list := list[0..n][..n] + list[n..list.Length];
}
// </vc-code>
