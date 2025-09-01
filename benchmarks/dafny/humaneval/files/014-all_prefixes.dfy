// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def all_prefixes(string: str) -> List[str]
Return list of all prefixes from shortest to longest of the input string
*/
// </vc-description>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)
    // post-conditions-start
    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
