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

// </vc-helpers>

// <vc-spec>
method ToToggleCase(str1: array<char>) returns (toggle_case: array<char>)
    ensures
        str1.Length == toggle_case.Length &&
        forall i :: 0 <= i < str1.Length ==> toggle_case[i] == ToToggleCaseSpec(str1[i])
// </vc-spec>
// <vc-code>
{
  toggle_case := new char[str1.Length];
  var i := 0;
  while i < str1.Length
    invariant 0 <= i <= str1.Length
    invariant forall j :: 0 <= j < i ==> toggle_case[j] == ToToggleCaseSpec(str1[j])
  {
    if IsLowerCase(str1[i]) {
      toggle_case[i] := ShiftMinus32Spec(str1[i]);
    } else if IsUpperCase(str1[i]) {
      toggle_case[i] := Shift32Spec(str1[i]);
    } else {
      toggle_case[i] := str1[i];
    }
    i := i + 1;
  }
}
// </vc-code>
