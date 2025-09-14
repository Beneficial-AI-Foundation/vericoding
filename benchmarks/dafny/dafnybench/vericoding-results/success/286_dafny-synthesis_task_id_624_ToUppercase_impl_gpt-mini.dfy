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
lemma IntCharRoundtrip(x: int)
  requires 0 <= x < 128
  ensures ((x as char) as int) == x
{
  assert 0 <= x;
  assert x < 128;
  assert ((x as char) as int) == x;
}

lemma LowerToUpper_chars(c: char)
  requires IsLowerCase(c)
  ensures IsLowerUpperPair(c, ((c as int - 32) as char))
{
  var x := c as int - 32;
  assert 65 <= x <= 90;
  assert 0 <= x < 128;
  IntCharRoundtrip(x);
  assert ((x as char) as int) == x;
  assert (c as int) == x + 32;
  assert (((c as int - 32) as char) as int) == (c as int - 32);
  assert (((c as int - 32) as char) as int) + 32 == c as int;
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var buf : seq<char> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |buf| == i
    invariant forall j :: 0 <= j < i ==>
      (if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], buf[j]) else buf[j] == s[j])
  {
    var c := s[i];
    if IsLowerCase(c) {
      var up := (c as int - 32) as char;
      buf := buf + [up];
      LowerToUpper_chars(c);
    } else {
      buf := buf + [c];
    }
    i := i + 1;
  }
  v := buf;
}
// </vc-code>

