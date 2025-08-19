//IMPL
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
  /* code modified by LLM (iteration 1): removed redundant null check since array<int> is non-null by default */
  ensures |r| == |s| + a.Length
  ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
  ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
{
  r := s + a[..];
}