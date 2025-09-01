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
function methodStrXor(a: string, b: string, i: nat): string
    requires |a| == |b|
    requires i <= |a|
    requires forall k :: 0 <= k < |a| ==> represents_byte(a[k])
    requires forall k :: 0 <= k < |b| ==> represents_byte(b[k])
    ensures |methodStrXor(a, b, i)| == i
    ensures forall k :: 0 <= k < i ==> methodStrXor(a, b, i)[k] == char_xor(a[k], b[k])
    ensures forall k :: 0 <= k < i ==> represents_byte(methodStrXor(a, b, i)[k])
    decreases i
{
    if i == 0 then
        ""
    else
        methodStrXor(a, b, i - 1) + (if char_xor(a[i - 1], b[i - 1]) == '0' then "0" else "1")
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
  result := methodStrXor(a, b, |a|);
}
// </vc-code>

