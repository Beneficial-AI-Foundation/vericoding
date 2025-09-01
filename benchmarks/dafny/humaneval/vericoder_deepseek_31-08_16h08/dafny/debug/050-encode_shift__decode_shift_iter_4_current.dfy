function encode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= encode_char(c) <= 'z'
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int + 5) % 26 + 'a' as int) as char
  // impl-end
}
function decode_char(c: char): char
  // pre-conditions-start
  requires 'a' <= c <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures 'a' <= decode_char(c) <= 'z'
  ensures encode_char(decode_char(c)) == c
  // post-conditions-end
{
  // impl-start
  ((c as int - 'a' as int - 5) % 26 + 'a' as int) as char
  // impl-end
}
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma {:vcs_split_on_every_assert} ModuloProperties(a: int, b: int)
  requires b > 0
  ensures 0 <= a % b <= b
{
  // Dafny knows modulo properties
}

lemma {:vcs_split_on_every_assert} CharRangeProperties()
  ensures forall c: char :: 'a' <= c <= 'z' ==> 0 <= c as int - 'a' as int <= 25
{
  forall c: char | 'a' <= c <= 'z'
    ensures 0 <= c as int - 'a' as int <= 25
  {
    // Dafny knows character arithmetic
  }
}

lemma {:vcs_split_on_every_assert} EncodeDecodeCorrectness()
  ensures forall c: char :: 'a' <= c <= 'z' ==> encode_char(decode_char(c)) == c
  ensures forall c: char :: 'a' <= c <= 'z' ==> decode_char(encode_char(c)) == c
{
  forall c: char | 'a' <= c <= 'z'
    ensures encode_char(decode_char(c)) == c
    ensures decode_char(encode_char(c)) == c
  {
    // Dafny can prove these properties
  }
}

lemma ModuloNegativeFix(n: int, m: int)
  requires m > 0
  ensures (n % m + m) % m == n % m
{
  // Helper lemma for negative modulo handling
  if n % m < 0 {
    assert (n % m + m) % m == n % m + m;
  }
}

lemma ModuloNonNegative(n: int, m: int)
  requires m > 0
  ensures 0 <= (n % m + m) % m < m
{
  assert 0 <= (n % m + m) % m;
  assert (n % m + m) % m < m;
}

lemma CharacterShiftCorrectness(c: char, shift: int)
  requires 'a' <= c <= 'z'
  requires 0 <= shift <= 25
  ensures 'a' <= (((c as int - 'a' as int - shift) % 26 + 26) % 26 + 'a' as int) as char <= 'z'
  ensures ((((c as int - 'a' as int - shift) % 26 + 26) % 26 + 'a' as int) as char) == decode_char(c)
{
  var shifted := c as int - 'a' as int - shift;
  var mod26 := shifted % 26;
  var positive_mod := (mod26 + 26) % 26;
  assert 0 <= positive_mod <= 25;
  var result := positive_mod + 'a' as int;
  assert 'a' as int <= result <= 'z' as int;
}
// </vc-helpers>

// <vc-spec>
method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  t := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == decode_char(s[j])
  {
    var c := s[i];
    var shifted := c as int - 'a' as int;
    var shifted2 := shifted - 5;
    var shifted3 := shifted2 % 26;
    if shifted3 < 0 {
      shifted3 := shifted3 + 26;
    }
    var shifted4 := shifted3 + 'a' as int;
    assert shifted4 as char == decode_char(c);
    t := t + [shifted4 as char];
    i := i + 1;
  }
}
// </vc-code>

