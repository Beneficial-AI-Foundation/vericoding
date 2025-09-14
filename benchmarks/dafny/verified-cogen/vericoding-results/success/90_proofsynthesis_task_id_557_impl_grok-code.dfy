// <vc-preamble>
predicate IsUpperCase(c: char)
{
    c >= 'A' && c <= 'Z'
}

function Shift32Spec(c: char): char
    requires c as int + 32 <= 127
{
    (c as int + 32) as char
}

predicate IsLowerCase(c: char)
{
    c >= 'a' && c <= 'z'
}

function ShiftMinus32Spec(c: char): char
    requires c as int - 32 >= 0 && c as int - 32 <= 127
{
    (c as int - 32) as char
}

function ToToggleCaseSpec(s: char): char
{
    if IsLowerCase(s) then
        ShiftMinus32Spec(s)
    else if IsUpperCase(s) then
        Shift32Spec(s)
    else
        s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no changes needed */
// </vc-helpers>

// <vc-spec>
method ToToggleCase(str1: array<char>) returns (toggle_case: array<char>)
    ensures
        str1.Length == toggle_case.Length &&
        forall i :: 0 <= i < str1.Length ==> toggle_case[i] == ToToggleCaseSpec(str1[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): added loop invariant to verify postcondition */
var result := new char[str1.Length];
var i := 0;
while i < str1.Length
  invariant 0 <= i <= str1.Length
  invariant forall k :: 0 <= k < i ==> result[k] == ToToggleCaseSpec(str1[k])
{
  var c := str1[i];
  if 'a' <= c <= 'z'
  {
    result[i] := ((c as int - 32) as char);
  }
  else if 'A' <= c <= 'Z'
  {
    result[i] := ((c as int + 32) as char);
  }
  else
  {
    result[i] := c;
  }
  i := i + 1;
}
toggle_case := result;
}
// </vc-code>
