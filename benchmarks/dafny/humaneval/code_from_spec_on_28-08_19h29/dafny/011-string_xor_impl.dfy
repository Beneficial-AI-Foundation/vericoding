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
// Helper function to check if a string consists only of 0s and 1s
function IsBinaryString(s: string): bool {
    forall i :: 0 <= i < |s| ==> represents_byte(s[i])
}

// Helper function to compute XOR of two binary strings character by character
function StringXorAux(a: string, b: string, i: int): string
    requires 0 <= i <= |a|
    requires |a| == |b|
    requires IsBinaryString(a)
    requires IsBinaryString(b)
    ensures |StringXorAux(a, b, i)| == i
    ensures forall k :: 0 <= k < i ==> StringXorAux(a, b, i)[k] == char_xor(a[k], b[k])
{
    if i == 0 then ""
    else StringXorAux(a, b, i-1) + [char_xor(a[i-1], b[i-1])]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def string_xor(a: str, b: str) -> str
Input are two strings a and b consisting only of 1s and 0s. Perform binary XOR on these inputs and return result also as a string.
*/
// </vc-description>

// <vc-spec>
method string_xor(a: string, b: string) returns (result: string)
    requires |a| == |b|
    requires IsBinaryString(a)
    requires IsBinaryString(b)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == char_xor(a[i], b[i])
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == char_xor(a[k], b[k])
    {
        result := result + [char_xor(a[i], b[i])];
        i := i + 1;
    }
}
// </vc-code>
