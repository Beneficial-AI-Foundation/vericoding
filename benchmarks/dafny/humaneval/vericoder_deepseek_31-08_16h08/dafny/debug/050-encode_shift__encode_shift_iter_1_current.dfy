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

// <vc-helpers>
lemma ComputeModProperties(c: char, k: int)
  requires 'a' <= c <= 'z'
  requires 0 < k
  ensures (c as int - 'a' as int) % k >= 0
  ensures (c as int - 'a' as int) % k < k
{
}

lemma EncodeDecodeProperties(c: char)
  requires 'a' <= c <= 'z'
  ensures -26 < (c as int - 'a' as int - 5) % 26 < 26
{
  var offset := c as int - 'a' as int;
  assert 0 <= offset < 26;
  
  if offset - 5 < 0 {
    assert (offset - 5) % 26 == 21 + offset;
    assert 21 <= 21 + offset <= 21 + 25;
  } else {
    assert (offset - 5) % 26 == offset - 5;
    assert 0 <= offset - 5 <= 20;
  }
}
// </vc-helpers>

// <vc-spec>
method encode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == encode_char(s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  t := "";
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == encode_char(s[j])
  {
    var encoded := encode_char(s[i]);
    t := t + [encoded];
    i := i + 1;
  }
}
// </vc-code>

method decode_shift(s: string) returns (t: string)
  // pre-conditions-start
  requires forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
  // pre-conditions-end
  // post-conditions-start
  ensures |s| == |t|
  ensures forall i :: 0 <= i < |s| ==> t[i] == decode_char(s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}