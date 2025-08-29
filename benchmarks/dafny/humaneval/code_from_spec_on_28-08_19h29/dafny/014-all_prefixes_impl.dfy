// <vc-helpers>
// Helper function to define a prefix of a string
ghost predicate IsPrefix(s: string, prefix: string)
{
  |prefix| <= |s| && prefix == s[..|prefix|]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def all_prefixes(string: str) -> List[str]
Return list of all prefixes from shortest to longest of the input string
*/
// </vc-description>

// <vc-spec>
method AllPrefixes(s: string) returns (prefixes: seq<string>)
  requires |s| >= 0
  ensures |prefixes| == |s| + 1
  ensures forall i :: 0 <= i < |prefixes| ==> IsPrefix(s, prefixes[i]) && |prefixes[i]| == i
  ensures forall i, j :: 0 <= i < j < |prefixes| ==> |prefixes[i]| < |prefixes[j]|
// </vc-spec>
// <vc-code>
{
  prefixes := [];
  var i := 0;
  while i <= |s|
    invariant 0 <= i <= |s| + 1
    invariant |prefixes| == i
    invariant forall k :: 0 <= k < i ==> IsPrefix(s, prefixes[k]) && |prefixes[k]| == k
  {
    if i == 0 {
      prefixes := prefixes + [""];
    } else {
      prefixes := prefixes + [s[..i]];
    }
    i := i + 1;
  }
}
// </vc-code>
