// <vc-preamble>
predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no change from previous turn, but adding comment as required */
function CharToLowercase(c: char): char
  ensures if IsUpperCase(c) then IsUpperLowerPair(c, CharToLowercase(c)) else CharToLowercase(c) == c
{
  if IsUpperCase(c) then (c as int + 32) as char else c
}
// </vc-helpers>

// <vc-spec>
method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added loop invariants for index bounds and termination, fixing proof failures. */
  v := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> v[j] == CharToLowercase(s[j])
    decreases |s| - i
  {
    v := v + [CharToLowercase(s[i])];
    i := i + 1;
  }
}
// </vc-code>
