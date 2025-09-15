// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method all_prefixes(s: string) returns (prefixes: seq<string>)

    ensures |prefixes| == |s|
    ensures forall i :: 0 <= i < |prefixes| ==> s[..i+1] == prefixes[i]
// </vc-spec>
// <vc-code>
{
  var prefixes_arr: array<string> := new string[|s|];

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[..k+1] == prefixes_arr[k]
  {
    prefixes_arr[i] := s[..i+1];
    i := i + 1;
  }

  prefixes := prefixes_arr[..];
}
// </vc-code>
