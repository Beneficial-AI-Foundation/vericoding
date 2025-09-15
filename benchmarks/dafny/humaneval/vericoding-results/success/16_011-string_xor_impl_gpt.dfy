// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function CharToString(c: char): string { [c] }
lemma CharXorByteLemma(a: char, b: char)
  requires represents_byte(a)
  requires represents_byte(b)
  ensures represents_byte(char_xor(a, b))
{ }
// </vc-helpers>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)

    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])

    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> represents_byte(result[i])
    ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := "";
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant |a| == |b|
    invariant forall j :: 0 <= j < |a| ==> represents_byte(a[j])
    invariant forall j :: 0 <= j < |b| ==> represents_byte(b[j])
    invariant forall j :: 0 <= j < i ==> result[j] == char_xor(a[j], b[j])
    invariant forall j :: 0 <= j < i ==> represents_byte(result[j])
    decreases |a| - i
  {
    var c := char_xor(a[i], b[i]);
    CharXorByteLemma(a[i], b[i]);
    result := result + CharToString(c);
    i := i + 1;
  }
}
// </vc-code>
