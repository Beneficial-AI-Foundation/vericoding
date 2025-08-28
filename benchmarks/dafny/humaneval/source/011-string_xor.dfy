function represents_byte(a: char) : bool
{
    a in "01"
}
// pure-end
function char_xor(a: char, b: char): char
    requires represents_byte(a)
    requires represents_byte(b)
{
    if (a == b) then
        '0'
    else
        '1'
}
// pure-end
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
{
    // impl-start
    result := "";
    for i := 0 to |a|
        // invariants-start
        invariant |result| == i
        invariant forall i :: 0 <= i < |a| ==> represents_byte(a[i])
        invariant forall i :: 0 <= i < |b| ==> represents_byte(b[i])
        invariant forall j :: 0 <= j < i ==> result[j] == char_xor(a[j], b[j])
        // invariants-end
    {
        var bitResult := char_xor(a[i], b[i]);
        result := result + [bitResult];
    }
    // impl-end
}
