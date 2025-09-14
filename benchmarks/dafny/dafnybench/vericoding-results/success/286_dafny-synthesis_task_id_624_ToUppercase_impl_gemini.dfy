// <vc-preamble>
predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): reviewed and confirmed pre-existing lemma is sufficient */
lemma ToUpperProperty(c: char)
    requires IsLowerCase(c)
    ensures IsLowerUpperPair(c, ShiftMinus32(c))
{}
// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed compilation errors by using .Length for array size and array slicing for string conversion */
{
  var chars := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant chars.Length == |s|
    invariant forall j :: 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], chars[j]) else chars[j] == s[j]
  {
    if IsLowerCase(s[i]) {
      ToUpperProperty(s[i]);
      chars[i] := ShiftMinus32(s[i]);
    } else {
      chars[i] := s[i];
    }
    i := i + 1;
  }
  v := chars[..];
}
// </vc-code>
