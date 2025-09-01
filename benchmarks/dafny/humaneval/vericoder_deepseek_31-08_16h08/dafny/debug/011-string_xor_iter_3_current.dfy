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
lemma {:induction false} StringXorLemma(a: string, b: string, result: string, n: int)
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> represents_byte(a[i])
    requires forall i :: 0 <= i < |b| ==> represents_byte(b[i])
    requires |result| == n
    requires 0 <= n <= |a|
    requires forall i :: 0 <= i < n ==> represents_byte(result[i])
    requires forall i :: 0 <= i < n ==> result[i] == char_xor(a[i], b[i])
    ensures |result| == n
    ensures forall i :: 0 <= i < n ==> represents_byte(result[i])
    ensures forall i :: 0 <= i < n ==> result[i] == char_xor(a[i], b[i])
{
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
    var length := |a|;
    var resultArray := new char[length];
    var i := 0;
    while i < length
        invariant 0 <= i <= length
        invariant resultArray.Length == length
        invariant forall j :: 0 <= j < i ==> represents_byte(resultArray[j])
        invariant forall j :: 0 <= j < i ==> resultArray[j] == char_xor(a[j], b[j])
    {
        resultArray[i] := char_xor(a[i], b[i]);
        i := i + 1;
    }
    result := resultArray[..];
}
// </vc-code>

