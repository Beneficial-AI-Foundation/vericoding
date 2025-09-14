// <vc-preamble>
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No changes needed, helper is correct. */
function ToggleChar(c: char): char
{
    if IsLowerCase(c) then ShiftMinus32(c)
    else if IsUpperCase(c) then Shift32(c)
    else c
}
// </vc-helpers>

// <vc-spec>
method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed string concatenation type error by wrapping char in a sequence. */
{
  v := "";
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> v[j] == ToggleChar(s[j])
  {
    v := v + [ToggleChar(s[i])];
    i := i + 1;
  }
}
// </vc-code>
