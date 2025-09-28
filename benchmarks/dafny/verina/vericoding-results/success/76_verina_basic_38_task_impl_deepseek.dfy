// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function AllSameFrom(s: seq<char>, start: int): bool
  requires 0 <= start <= |s|
  ensures AllSameFrom(s, start) ==> (forall j: int :: start <= j < |s| ==> s[j] == s[start])
  ensures !AllSameFrom(s, start) ==> (exists j: int :: start <= j < |s| && s[j] != s[start])
{
  if start == |s| then
    true
  else
    (forall j: int | start <= j < |s| :: s[j] == s[start])
}

// </vc-helpers>

// <vc-spec>
method AllCharactersSame(s: seq<char>) returns (result: bool)
    requires true
    ensures result ==> (forall i: int, j: int :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j])
    ensures !result ==> (|s| > 0 && exists i: int :: 0 <= i < |s| && s[i] != s[0])
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    result := true;
  } else {
    result := AllSameFrom(s, 0);
  }
}
// </vc-code>
