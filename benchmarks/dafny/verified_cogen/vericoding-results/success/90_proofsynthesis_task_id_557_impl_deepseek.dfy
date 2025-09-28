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
function Shift32Impl(c: char): char
  requires c as int + 32 <= 127
  ensures Shift32Impl(c) == Shift32Spec(c)
{
    (c as int + 32) as char
}

function ShiftMinus32Impl(c: char): char
  requires c as int - 32 >= 0 && c as int - 32 <= 127
  ensures ShiftMinus32Impl(c) == ShiftMinus32Spec(c)
{
    (c as int - 32) as char
}

/* helper modified by LLM (iteration 3): Added ensures clauses to forall statements */
lemma ShiftTransformsCaseUptoLC()
  ensures forall c :: IsUpperCase(c) ==> Shift32Impl(c) as int >= 'a' as int && Shift32Impl(c) as int <= 'z' as int
{
  forall c | IsUpperCase(c)
    ensures Shift32Impl(c) as int >= 'a' as int && Shift32Impl(c) as int <= 'z' as int
  {
    assert Shift32Impl(c) as int == c as int + 32;
    assert c as int >= 'A' as int && c as int <= 'Z' as int;
    assert Shift32Impl(c) as int >= 'A' as int + 32;
    assert Shift32Impl(c) as int <= 'Z' as int + 32;
    assert 'A' as int + 32 == 'a' as int;
    assert 'Z' as int + 32 == 'z' as int;
  }
}

/* helper modified by LLM (iteration 3): Added ensures clauses to forall statements */
lemma ShiftTransformsCaseLtoUC()
  ensures forall c :: IsLowerCase(c) ==> ShiftMinus32Impl(c) as int >= 'A' as int && ShiftMinus32Impl(c) as int <= 'Z' as int
{
  forall c | IsLowerCase(c)
    ensures ShiftMinus32Impl(c) as int >= 'A' as int && ShiftMinus32Impl(c) as int <= 'Z' as int
  {
    assert ShiftMinus32Impl(c) as int == c as int - 32;
    assert c as int >= 'a' as int && c as int <= 'z' as int;
    assert ShiftMinus32Impl(c) as int >= 'a' as int - 32;
    assert ShiftMinus32Impl(c) as int <= 'z' as int - 32;
    assert 'a' as int - 32 == 'A' as int;
    assert 'z' as int - 32 == 'Z' as int;
  }
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
  /* code modified by LLM (iteration 3): No changes needed, code already verifies */
  toggle_case := new char[str1.Length];
  var index := 0;
  while index < str1.Length
      invariant 0 <= index <= str1.Length
      invariant toggle_case.Length == str1.Length
      invariant forall i :: 0 <= i < index ==> toggle_case[i] == ToToggleCaseSpec(str1[i])
  {
      var origChar := str1[index];
      if IsLowerCase(origChar) {
          toggle_case[index] := ShiftMinus32Impl(origChar);
      } else if IsUpperCase(origChar) {
          toggle_case[index] := Shift32Impl(origChar);
      } else {
          toggle_case[index] := origChar;
      }
      index := index + 1;
  }
}
// </vc-code>
