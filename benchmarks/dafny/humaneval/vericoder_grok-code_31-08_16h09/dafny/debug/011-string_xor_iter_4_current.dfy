function represents_byte(a: char) : bool
{
    a in "01"
}
function char_xor(a: char, b: char): char
    requires represents_byte(a)
    requires represents_byte(b)
{
    if (a == b) then
        '0'
    else
        '1'
}

// <vc-helpers>
function represents_byte(a: char) : bool
{
    a in "01"
}
function char_xor(a: char, b: char): char
    requires represents_byte(a)
    requires represents_byte(b)
{
    if (a == b) then
        '0'
    else
        '1'
}
// </vc-helpers>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)
    // pre-conditions-start
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])
    // pre-conditions-end
    // post-conditions-start
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> represents_byte(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
    // post-conditions-end
// </vc-spec>
// <vc-code>
var res: seq<char> := [];
  for i := 0 to |a| - 1
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == char_xor(a[k], b[k])
    invariant forall k :: 0 <= k < |res| ==> represents_byte(res[k])
  {
    var xor_char := char_xor(a[i], b[i]);
    res := res + [xor_char];
  }
  result := res;
// </vc-code>

