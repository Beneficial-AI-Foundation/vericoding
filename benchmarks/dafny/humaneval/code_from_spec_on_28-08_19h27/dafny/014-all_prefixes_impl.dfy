// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def all_prefixes(string: str) -> List[str]
Return list of all prefixes from shortest to longest of the input string
*/
// </vc-description>

// <vc-spec>
method AllPrefixes(s: string) returns (prefixes: seq<string>)
  ensures |prefixes| == |s| + 1
  ensures forall i :: 0 <= i < |prefixes| ==> prefixes[i] == s[0..i]
  ensures forall i, j :: 0 <= i < j < |prefixes| ==> |prefixes[i]| < |prefixes[j]|
// </vc-spec>
// <vc-code>
{
  prefixes := [];
  var i := 0;
  while i <= |s|
    invariant 0 <= i <= |s| + 1
    invariant |prefixes| == i
    invariant forall k :: 0 <= k < i ==> prefixes[k] == s[0..k]
  {
    prefixes := prefixes + [s[0..i]];
    i := i + 1;
  }
}
// </vc-code>
