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
lemma CharIntRoundTrip(i: int)
  requires 0 <= i < 256
  ensures ((i as char) as int) == i
{
  assert 0 <= i < 256;
  assert ((i as char) as int) == i;
}
// </vc-helpers>

// <vc-spec>
method ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var res: string := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==>
      (if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], res[j])
       else if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], res[j])
       else res[j] == s[j])
    decreases |s| - i
  {
    var ch := s[i];
    var newCh: char;
    if IsLowerCase(ch) {
      assert 97 <= ch as int <= 122;
      assert 65 <= (ch as int) - 32 <= 90;
      assert 0 <= (ch as int) - 32 < 256;
      newCh := ((ch as int) - 32) as char;
      CharIntRoundTrip((ch as int) - 32);
      assert (newCh as int) == (ch as int) - 32;
      assert IsLowerUpperPair(ch, newCh);
    } else if IsUpperCase(ch) {
      assert 65 <= ch as int <= 90;
      assert 97 <= (ch as int) + 32 <= 122;
      assert 0 <= (ch as int) + 32 < 256;
      newCh := ((ch as int) + 32) as char;
      CharIntRoundTrip((ch as int) + 32);
      assert (newCh as int) == (ch as int) + 32;
      assert IsUpperLowerPair(ch, newCh);
    } else {
      newCh := ch;
      assert newCh == ch;
    }
    var oldRes := res;
    res := res + [newCh];
    assert |res| == |oldRes| + 1;
    assert res[|oldRes|] == newCh;
    i := i + 1;
    assert |oldRes| == i - 1;
    assert res[i - 1] == newCh;
    assert if IsLowerCase(ch) then IsLowerUpperPair(ch, res[i - 1])
           else if IsUpperCase(ch) then IsUpperLowerPair(ch, res[i - 1])
           else res[i - 1] == ch;
  }
  v := res;
}
// </vc-code>

