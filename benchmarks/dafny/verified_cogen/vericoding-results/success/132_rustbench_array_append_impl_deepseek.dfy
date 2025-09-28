// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SeqAppendOne<T>(s: seq<T>, x: T): seq<T>
  ensures |SeqAppendOne(s, x)| == |s| + 1
  ensures forall i :: 0 <= i < |s| + 1 ==> SeqAppendOne(s, x)[i] == (if i < |s| then s[i] else x)
{
  s + [x]
}

lemma SeqAppendOneLemma<T>(s: seq<T>, x: T, i: int)
  requires 0 <= i < |s| + 1
  ensures SeqAppendOne(s, x)[i] == (if i < |s| then s[i] else x)
{
  // Built-in sequence concatenation properties automatically verify this
}
// </vc-helpers>

// <vc-spec>
method ArrayAppend(a: seq<int>, b: int) returns (result: seq<int>)
    ensures |result| == |a| + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == (if i < |a| then a[i] else b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by using built-in sequence concatenation */
  result := a + [b];
}
// </vc-code>
