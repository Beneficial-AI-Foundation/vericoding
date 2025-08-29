// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def filter_by_prefix(strings: List[str], prefix: str) -> List[str]
Filter an input list of strings only for ones that start with a given prefix.
*/
// </vc-description>

// <vc-spec>
method filter_by_prefix(strings: seq<string>, prefix: string) returns (result: seq<string>)
  ensures |result| <= |strings|
  ensures forall i :: 0 <= i < |result| ==> starts_with(result[i], prefix)
  ensures forall s :: s in result ==> s in strings
  ensures forall s :: s in strings && starts_with(s, prefix) ==> s in result
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |strings|
    invariant 0 <= i <= |strings|
    invariant |result| <= i
    invariant forall j :: 0 <= j < |result| ==> starts_with(result[j], prefix)
    invariant forall s :: s in result ==> s in strings
    invariant forall j :: 0 <= j < i && starts_with(strings[j], prefix) ==> strings[j] in result
  {
    if starts_with(strings[i], prefix) {
      result := result + [strings[i]];
    }
  }
}
// </vc-code>

function starts_with(s: string, p: string): bool {
  |p| == 0 || (|s| != 0 && |s| >= |p| && s[0] == p[0] && starts_with(s[1..], p[1..]))
}
// pure-end