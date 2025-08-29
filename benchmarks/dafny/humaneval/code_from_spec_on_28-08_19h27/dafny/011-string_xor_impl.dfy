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
function string_xor_rec(a: string, b: string, i: nat): string
    requires |a| == |b|
    requires i <= |a|
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    decreases |a| - i
{
    if i == |a| then ""
    else [char_xor(a[i], b[i])] + string_xor_rec(a, b, i + 1)
}

lemma string_xor_rec_length(a: string, b: string, i: nat)
    requires |a| == |b|
    requires i <= |a|
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    ensures |string_xor_rec(a, b, i)| == |a| - i
    decreases |a| - i
{
    if i == |a| {
    } else {
        string_xor_rec_length(a, b, i + 1);
    }
}

lemma string_xor_rec_valid_bytes(a: string, b: string, i: nat)
    requires |a| == |b|
    requires i <= |a|
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    ensures forall k :: 0 <= k < |string_xor_rec(a, b, i)| ==> represents_byte(string_xor_rec(a, b, i)[k])
    decreases |a| - i
{
    if i == |a| {
    } else {
        assert represents_byte(char_xor(a[i], b[i]));
        string_xor_rec_valid_bytes(a, b, i + 1);
    }
}

lemma string_xor_rec_mapping(a: string, b: string, i: nat)
    requires |a| == |b|
    requires i <= |a|
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    ensures forall k :: 0 <= k < |string_xor_rec(a, b, i)| && i + k < |a| ==> string_xor_rec(a, b, i)[k] == char_xor(a[i + k], b[i + k])
    decreases |a| - i
{
    if i == |a| {
    } else {
        string_xor_rec_mapping(a, b, i + 1);
    }
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
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    ensures |result| == |a|
    ensures forall k :: 0 <= k < |result| ==> represents_byte(result[k])
    ensures forall k :: 0 <= k < |result| ==> result[k] == char_xor(a[k], b[k])
// </vc-spec>
// <vc-code>
{
    result := string_xor_rec(a, b, 0);
    string_xor_rec_length(a, b, 0);
    string_xor_rec_valid_bytes(a, b, 0);
    string_xor_rec_mapping(a, b, 0);
}
// </vc-code>
