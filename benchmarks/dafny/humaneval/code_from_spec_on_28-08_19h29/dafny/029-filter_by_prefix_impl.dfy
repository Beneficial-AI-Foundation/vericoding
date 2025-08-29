// <vc-helpers>
// Helper predicate to check if a string starts with a given prefix
function StartsWith(s: string, p: string): bool {
  |p| == 0 || (|s| >= |p| && s[..|p|] == p)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def filter_by_prefix(strings: List[str], prefix: str) -> List[str]
Filter an input list of strings only for ones that start with a given prefix.
*/
// </vc-description>

// <vc-spec>
method FilterByPrefix(strings: seq<string>, prefix: string) returns (result: seq<string>)
  ensures forall i :: 0 <= i < |result| ==> StartsWith(result[i], prefix)
  ensures forall s :: s in strings && StartsWith(s, prefix) ==> s in result
  ensures forall s :: s in result ==> s in strings
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |strings|
    invariant 0 <= i <= |strings|
    invariant forall j :: 0 <= j < |result| ==> StartsWith(result[j], prefix)
    invariant forall s :: s in strings[..i] && StartsWith(s, prefix) ==> s in result
    invariant forall s :: s in result ==> s in strings[..i]
  {
    if StartsWith(strings[i], prefix) {
      result := result + [strings[i]];
    }
  }
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end