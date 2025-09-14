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

// <vc-helpers>
lemma Shift32_UpperLowerPair(c: char)
  requires IsUpperCase(c)
  ensures IsUpperLowerPair(c, Shift32(c))
{
  var x := c as int;
  assert (c as int) == x;
  assert 65 <= x <= 90;
  assert 0 <= x + 32;
  assert x + 32 < 128;
  assert (Shift32(c) as int) == ((x + 32) % 128);
  assert ((x + 32) % 128) == x + 32;
  assert (Shift32(c) as int) == x + 32;
  assert (c as int) == (Shift32(c) as int) - 32;
}
// </vc-helpers>

// <vc-spec>
method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var a := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> (if IsUpperCase(s[j]) then IsUpperLowerPair(s[j], a[j]) else a[j] == s[j])
    decreases n - i
  {
    var ch := s[i];
    if IsUpperCase(ch) {
      a[i] := Shift32(ch);
      Shift32_UpperLowerPair(ch);
      assert a[i] == Shift32(ch);
      assert IsUpperLowerPair(ch, a[i]);
    } else {
      a[i] := ch;
    }
    i := i + 1;
  }
  v := a[..];
}
// </vc-code>

