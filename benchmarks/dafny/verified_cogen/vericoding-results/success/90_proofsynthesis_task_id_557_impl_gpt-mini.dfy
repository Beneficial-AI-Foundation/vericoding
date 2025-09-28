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
lemma UpperCaseShiftSafe(c: char)
    requires IsUpperCase(c)
    ensures c as int + 32 <= 127
{
    // From IsUpperCase(c): c >= 'A' && c <= 'Z'
    assert c as int <= 'Z' as int;
    assert c as int + 32 <= 'Z' as int + 32;
    assert 'Z' as int + 32 <= 127;
    assert c as int + 32 <= 127;
}

lemma LowerCaseShiftSafe(c: char)
    requires IsLowerCase(c)
    ensures c as int - 32 >= 0 && c as int - 32 <= 127
{
    // From IsLowerCase(c): c >= 'a' && c <= 'z'
    assert c as int >= 'a' as int;
    assert c as int - 32 >= 'a' as int - 32;
    assert 'a' as int - 32 >= 0;
    assert c as int - 32 >= 0;
    assert c as int <= 'z' as int;
    assert c as int - 32 <= 'z' as int - 32;
    assert 'z' as int - 32 <= 127;
    assert c as int - 32 <= 127;
}
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
    var c := str1[i];
    if IsLowerCase(c) {
      LowerCaseShiftSafe(c);
      toggle_case[i] := ShiftMinus32Spec(c);
    } else if IsUpperCase(c) {
      UpperCaseShiftSafe(c);
      toggle_case[i] := Shift32Spec(c);
    } else {
      toggle_case[i] := c;
    }
    i := i + 1;
  }
}
// </vc-code>
