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

// <vc-helpers>
lemma LemmaShiftMinus32(c: char)
  ensures IsLowerCase(c) ==> IsLowerUpperPair(c, ShiftMinus32(c))
{
  if IsLowerCase(c) {
    var ci := c as int;
    assert 97 <= ci <= 122;
    var diff := ci - 32;
    assert 0 <= diff <= 127;
    assert (diff % 128) == diff;
    assert (ShiftMinus32(c) as int) == diff % 128;
    assert (ShiftMinus32(c) as int) + 32 == diff + 32;
    assert (ShiftMinus32(c) as int) + 32 == ci;
  }
}

lemma LemmaShift32(c: char)
  ensures IsUpperCase(c) ==> IsUpperLowerPair(c, Shift32(c))
{
  if IsUpperCase(c) {
    var ci := c as int;
    assert 65 <= ci <= 90;
    var sum := ci + 32;
    assert 0 <= sum <= 127;
    assert (sum % 128) == sum;
    assert (Shift32(c) as int) == sum % 128;
    assert (Shift32(c) as int) - 32 == sum - 32;
    assert (Shift32(c) as int) - 32 == ci;
  }
}
// </vc-helpers>

// <vc-spec>
method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var res := "";
  var i := 0;
  while i < |s|
    decreases |s| - i
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==>
        if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], res[j])
        else if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], res[j])
        else res[j] == s[j]
  {
    var c := s[i];
    if IsLowerCase(c) {
      LemmaShiftMinus32(c);
      res := res + [ShiftMinus32(c)];
      assert res[i] == ShiftMinus32(c);
    } else if IsUpperCase(c) {
      LemmaShift32(c);
      res := res + [Shift32(c)];
      assert res[i] == Shift32(c);
    } else {
      res := res + [c];
      assert res[i] == c;
    }
    i := i + 1;
  }
  v := res;
}
// </vc-code>

