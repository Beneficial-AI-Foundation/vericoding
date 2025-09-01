

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
  for i := 0 to |s|-1 {
    prefixes_array[i] := s[..i+1];
  }
  return prefixes_array[..];
}
// </vc-code>

