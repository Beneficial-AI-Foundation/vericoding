

// <vc-helpers>
lemma Lemma_AppendSubsequence(s: string, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
}

lemma Lemma_AllPrefixesEmpty(s: string)
  ensures |s| == 0 ==> all_prefixes(s) == []
{
}

function all_prefixes(s: string): seq<string>
  ensures |all_prefixes(s)| == |s|
  ensures forall i :: 0 <= i < |all_prefixes(s)| ==> all_prefixes(s)[i] == s[..i+1]
{
  if |s| == 0 then []
  else 
    var rest := all_prefixes(s[1..]);
    [s[..1]] + [s[..k+2] | k in 0..|rest|-1]
}
// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)
    // post-conditions-start
    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    prefixes := [];
  } else {
    var p := all_prefixes(s[1..]);
    prefixes := [s[..1]];
    var i := 0;
    while i < |p|
      invariant |prefixes| == i + 1
      invariant forall j :: 0 <= j <= i ==> prefixes[j] == s[..j+1]
    {
      prefixes := prefixes + [s[..i+2]];
      i := i + 1;
    }
  }
}
// </vc-code>

