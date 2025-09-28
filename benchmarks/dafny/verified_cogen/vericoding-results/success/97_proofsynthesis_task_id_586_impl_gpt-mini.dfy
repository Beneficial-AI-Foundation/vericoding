// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed lemmas by removing reads clauses and provided ArraySeq function */
function ArraySeq(a: array<int>): seq<int> reads a { a[..] }
lemma SeqLengthFromArray(a: array<int>) ensures |ArraySeq(a)| == a.Length { assert |ArraySeq(a)| == a.Length; }
lemma SliceEquality(a: array<int>, i: int, j: int) requires 0 <= i <= j <= a.Length ensures ArraySeq(a)[i..j] == a[i..j] { assert ArraySeq(a)[i..j] == a[i..j]; }
// </vc-helpers>

// <vc-spec>
method SplitAndAppend(list: array<int>, n: int) returns (new_list: seq<int>)
    requires list.Length > 0
    requires 0 < n < list.Length
    ensures new_list == list[n..list.Length] + list[0..n]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): build sequence from array and use lemmas to relate slices */
  var s := ArraySeq(list);
  SliceEquality(list, n, list.Length);
  SliceEquality(list, 0, n);
  new_list := s[n..list.Length] + s[0..n];
}
// </vc-code>
