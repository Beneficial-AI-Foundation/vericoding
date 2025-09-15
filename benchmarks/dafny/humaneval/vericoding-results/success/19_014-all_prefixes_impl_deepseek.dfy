// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function prefixSeq(s: string, length: int): string
  requires 0 <= length <= |s|
{
  s[..length]
}

lemma PrefixLemma(s: string, i: int)
  requires 0 <= i <= |s|
  ensures s[..i] == prefixSeq(s, i)
{
}
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)

    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
// </vc-spec>
// <vc-code>
{
  prefixes := [];
  var n := |s|;
  var pos := 0;
  
  while pos < n
    invariant 0 <= pos <= n
    invariant |prefixes| == pos
    invariant forall j :: 0 <= j < pos ==> s[..j+1] == prefixes[j]
  {
    prefixes := prefixes + [s[..pos+1]];
    pos := pos + 1;
  }
}
// </vc-code>
