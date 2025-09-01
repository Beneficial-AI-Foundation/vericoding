

// <vc-helpers>

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
  var prefixes_array := new string[|s|];
  if |s| > 0 {
    for i := 0 to |s|-1
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> prefixes_array[j] == s[..j+1]
    {
      prefixes_array[i] := s[..i+1];
    }
  }
  return prefixes_array[..];
}
// </vc-code>

