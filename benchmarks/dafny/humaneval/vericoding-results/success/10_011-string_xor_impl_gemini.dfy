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
/* helper modified by LLM (iteration 3): named the return value to fix compilation errors */
function seq_char_xor(a: seq<char>, b: seq<char>): (res: seq<char>)
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])
    ensures |res| == |a|
    ensures forall i :: 0 <= i < |res| ==> res[i] == char_xor(a[i], b[i])
    ensures forall i :: 0 <= i < |res| ==> represents_byte(res[i])
    decreases |a|
{
    if |a| == 0 then [] else [char_xor(a[0], b[0])] + seq_char_xor(a[1..], b[1..])
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
{
  /* code modified by LLM (iteration 3): call the fixed helper function */
  result := seq_char_xor(a[..], b[..]);
}
// </vc-code>
