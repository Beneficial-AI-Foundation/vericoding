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
lemma Shift32_IsUpperLowerPair(C: char)
    requires IsUpperCase(C)
    ensures IsUpperLowerPair(C, Shift32(C))
{
    // From 65 <= C <= 90, we have 0 <= C+32 < 128, so modulo 128 is just C+32.
    assert 0 <= (C as int) + 32 && (C as int) + 32 < 128;
    assert (Shift32(C) as int) == ((C as int) + 32) % 128;
    assert ((C as int) + 32) % 128 == (C as int) + 32;
    assert (Shift32(C) as int) == (C as int) + 32;
    assert (Shift32(C) as int) - 32 == C as int;
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
    invariant a.Length == n
    invariant forall k :: 0 <= k < i ==>
      if IsUpperCase(s[k]) then IsUpperLowerPair(s[k], a[k]) else a[k] == s[k]
  {
    var c := s[i];
    if IsUpperCase(c) {
      a[i] := Shift32(c);
      assert a[i] == Shift32(c);
      Shift32_IsUpperLowerPair(c);
      assert IsUpperLowerPair(c, a[i]);
    } else {
      a[i] := c;
      assert a[i] == s[i];
    }
    i := i + 1;
  }
  v := a[..];
  return;
}
// </vc-code>

