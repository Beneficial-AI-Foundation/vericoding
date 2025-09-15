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
/* helper modified by LLM (iteration 5): Simplified helpers and removed unnecessary lemmas */
function string_of_chars(s: seq<char>): string
lemma xor_represents(a: char, b: char)
  requires represents_byte(a) && represents_byte(b)
  ensures represents_byte(char_xor(a, b))
{
}
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
/* code modified by LLM (iteration 5): Fixed string conversion and verification */
{
  var n := |a|;
  var res: seq<char> := [];
  var i := 0;
  
  while (i < n)
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> represents_byte(res[j])
    invariant forall j :: 0 <= j < i ==> res[j] == char_xor(a[j], b[j])
  {
    xor_represents(a[i], b[i]);
    res := res + [char_xor(a[i], b[i])];
    i := i + 1;
  }
  
  result := res;
}
// </vc-code>
