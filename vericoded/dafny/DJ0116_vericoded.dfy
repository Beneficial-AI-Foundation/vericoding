// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): trivial lemma about prefix slices */
lemma PrefixSliceIdentity(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  ensures s[0..n][..n] == s[0..n]
{
}

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
  /* code modified by LLM (iteration 3): return full array as sequence to satisfy postcondition */
  reversed_list := list[..];
}

// </vc-code>
