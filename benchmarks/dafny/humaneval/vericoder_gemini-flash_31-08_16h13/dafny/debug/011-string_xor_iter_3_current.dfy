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
function char_at(s: string, i: int): char
  requires 0 <= i < |s|
{
  s[i]
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
{
    var result_chars := new char[|a|];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result_chars| == |a|
        invariant forall j :: 0 <= j < i ==> represents_byte(result_chars[j])
        invariant forall j :: 0 <= j < i ==> result_chars[j] == char_xor(a[j], b[j])
        invariant forall j :: i <= j < |a| ==> result_chars[j] == char(0) // Default value for char array
    {
        result_chars[i] := char_xor(a[i], b[i]);
        i := i + 1;
    }
    result := new string(result_chars);
}
// </vc-code>

