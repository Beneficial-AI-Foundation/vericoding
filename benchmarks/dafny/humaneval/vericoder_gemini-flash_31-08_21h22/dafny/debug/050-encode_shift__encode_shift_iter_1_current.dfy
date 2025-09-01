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
function method char_to_int(c: char): int
  requires 'a' <= c <= 'z'
{
  c as int - 'a' as int
}

function method int_to_char(i: int): char
  requires 0 <= i <= 25
{
  (i + 'a' as int) as char
}

// Proof that encode_char is well-behaved
lemma EncodeCharProperties(c: char)
  requires 'a' <= c <= 'z'
  ensures 'a' <= encode_char(c) <= 'z'
  ensures char_to_int(encode_char(c)) == (char_to_int(c) + 5) % 26
{
  var c_int := char_to_int(c);
  // 0 <= c_int <= 25
  var encoded_int := (c_int + 5) % 26;
  // 0 <= encoded_int < 26
  var encoded_char := int_to_char(encoded_int);
  // 'a' <= encoded_char <= 'z'
  assert encoded_char == encode_char(c);
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
  var chars := new char[|s|];
  for k := 0 to |s|
    invariant 0 <= k <= |s|
    invariant forall i :: 0 <= i < k ==> 'a' <= s[i] <= 'z'
    invariant forall i :: 0 <= i < k ==> 'a' <= chars[i] <= 'z'
    invariant forall i :: 0 <= i < k ==> chars[i] == encode_char(s[i])
  {
    EncodeCharProperties(s[k]);
    chars[k] := encode_char(s[k]);
  }
  return new string(chars);
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