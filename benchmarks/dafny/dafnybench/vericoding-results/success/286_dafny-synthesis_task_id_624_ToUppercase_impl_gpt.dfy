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

// <vc-helpers>
lemma LowerUpperPairByShift(c: char)
  requires IsLowerCase(c)
  ensures IsLowerUpperPair(c, ShiftMinus32(c))
{
  var ci := c as int;
  assert 97 <= ci <= 122;
  assert 0 <= ci - 32;
  assert ci - 32 < 128;
  assert ((ci - 32) % 128) == ci - 32;
  assert (ShiftMinus32(c) as int) == ((c as int - 32) % 128);
  assert (c as int) == (ShiftMinus32(c) as int) + 32;
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  v := s;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == |s|
    invariant forall j :: 0 <= j < i ==> (if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], v[j]) else v[j] == s[j])
    invariant forall j :: i <= j < |s| ==> v[j] == s[j]
    decreases |s| - i
  {
    var c := s[i];
    var newCh := if IsLowerCase(c) then ShiftMinus32(c) else c;
    if IsLowerCase(c) {
      assert IsLowerUpperPair(c, ShiftMinus32(c)) by { LowerUpperPairByShift(c); }
    } else {
      assert newCh == c;
    }
    assert i + 1 <= |v|;
    v := v[..i] + [newCh] + v[i+1..];
    assert v[i] == newCh;
    i := i + 1;
  }
}
// </vc-code>

