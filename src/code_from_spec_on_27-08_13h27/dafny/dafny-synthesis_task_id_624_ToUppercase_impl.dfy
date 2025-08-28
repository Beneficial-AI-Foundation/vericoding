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
lemma ShiftMinus32Correct(c: char)
  requires IsLowerCase(c)
  ensures IsLowerUpperPair(c, ShiftMinus32(c))
{
  assert c as int >= 97 && c as int <= 122;
  var upper := ShiftMinus32(c);
  assert upper as int == (c as int - 32) % 128;
  assert upper as int == c as int - 32;
  assert (c as int) == (upper as int) + 32;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ToUppercaseImpl(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
  v := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |v| == i
    invariant forall j :: 0 <= j < i ==> if IsLowerCase(s[j]) then IsLowerUpperPair(s[j], v[j]) else v[j] == s[j]
  {
    if IsLowerCase(s[i]) {
      var upper := ShiftMinus32(s[i]);
      ShiftMinus32Correct(s[i]);
      v := v + [upper];
    } else {
      v := v + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
