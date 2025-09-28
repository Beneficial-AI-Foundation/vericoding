// <vc-preamble>

predicate ValidPrefixes(s: string, result: seq<string>)
{
    |result| == |s| &&
    forall i :: 0 <= i < |result| ==> result[i] == s[0..i+1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple lemmas about sequence snoc used implicitly by the loop proof */
lemma LemmaSnocLength<T>(xs: seq<T>, x: T)
  ensures |xs + [x]| == |xs| + 1
{
}

lemma LemmaSnocIndex<T>(xs: seq<T>, x: T, i: int)
  requires 0 <= i < |xs|
  ensures (xs + [x])[i] == xs[i]
{
}
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (result: seq<string>)
    ensures ValidPrefixes(s, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build all prefixes iteratively with loop invariants */
  var res: seq<string> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j] == s[0..j+1]
  {
    res := res + [s[0..i+1]];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
