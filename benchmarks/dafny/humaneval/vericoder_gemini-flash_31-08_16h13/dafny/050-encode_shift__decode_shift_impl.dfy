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
function char_at_index(s: string, i: int): char
  requires 0 <= i < |s|
{ s[i] }
lemma CreateString(arr: array<char>) returns (s: string)
  ensures |s| == arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> s[i] == arr[i]
{
  s := new string(arr);
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
    var char_array := new char[|s|];
    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> 'a' <= s[j] <= 'z'
        invariant forall j :: 0 <= j < i ==> char_array[j] == decode_char(s[j])
    {
        char_array[i] := decode_char(s[i]);
    }
    t := new string(char_array);
}
// </vc-code>

