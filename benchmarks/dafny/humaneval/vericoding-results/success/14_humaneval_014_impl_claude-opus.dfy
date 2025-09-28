// <vc-preamble>

predicate ValidPrefixes(s: string, result: seq<string>)
{
    |result| == |s| &&
    forall i :: 0 <= i < |result| ==> result[i] == s[0..i+1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (result: seq<string>)
    ensures ValidPrefixes(s, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == s[0..j+1]
  {
    result := result + [s[0..i+1]];
    i := i + 1;
  }
}
// </vc-code>
