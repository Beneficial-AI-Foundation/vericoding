

// <vc-helpers>
lemma {:induction false} SeqSliceProperties<T>(s: seq<T>, start: int, len: int)
  requires 0 <= start <= start + len <= |s|
  ensures |s[start..start+len]| == len
  ensures forall i {:trigger s[start + i]} :: 0 <= i < len ==> s[start..start+len][i] == s[start + i]
{}

lemma {:induction false} SeqConcatProperties<T>(s1: seq<T>, s2: seq<T>)
  ensures |s1 + s2| == |s1| + |s2|
  ensures forall i :: 0 <= i < |s1| ==> (s1 + s2)[i] == s1[i]
  ensures forall i :: |s1| <= i < |s1| + |s2| ==> (s1 + s2)[i] == s2[i - |s1|]
{}

lemma {:induction false} SeqTakeProperties<T>(s: seq<T>, n: int)
  requires 0 <= n <= |s|
  ensures |s[..n]| == n
  ensures forall i :: 0 <= i < n ==> s[..n][i] == s[i]
{}

lemma {:induction false} ReplaceLastElementLemma(first: seq<int>, second: seq<int>, result: seq<int>)
  requires |first| > 0
  requires result == first[..|first| - 1] + second
  ensures |result| == |first| - 1 + |second|
  ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
  ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
{
  var prefix := first[..|first| - 1];
  assert |result| == |prefix| + |second|;
  assert |prefix| == |first| - 1;
  SeqTakeProperties(first, |first| - 1);
  SeqConcatProperties(prefix, second);
}
// </vc-helpers>

// <vc-spec>
method ReplaceLastElement(first: seq<int>, second: seq<int>) returns (result: seq<int>)
    requires |first| > 0
    ensures |result| == |first| - 1 + |second|
    ensures forall i :: 0 <= i < |first| - 1 ==> result[i] == first[i]
    ensures forall i :: |first| - 1 <= i < |result| ==> result[i] == second[i - |first| + 1]
// </vc-spec>
// <vc-code>
{
  var prefix := first[..|first| - 1];
  result := prefix + second;
  
  // Explicitly assert the postconditions to help the verifier
  assert |result| == |first| - 1 + |second|;
  
  forall i | 0 <= i < |first| - 1
    ensures result[i] == first[i]
  {
    // Trigger the quantifier in SeqConcatProperties
    SeqConcatProperties(prefix, second);
  }
  
  forall i | |first| - 1 <= i < |result|
    ensures result[i] == second[i - |first| + 1]
  {
    // Trigger the quantifier in SeqConcatProperties
    SeqConcatProperties(prefix, second);
  }
  
  ReplaceLastElementLemma(first, second, result);
}
// </vc-code>

