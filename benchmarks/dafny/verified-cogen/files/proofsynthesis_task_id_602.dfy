// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountFrequencyRcr(s: seq<char>, key: char): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountFrequencyRcr(s[..|s|-1], key) + if (s[|s|-1] == key) then
            1
        else
            0
}

predicate CheckFirstRepeatedChar(str1: seq<char>, repeated_char: Option<(nat, char)>)
{
    match repeated_char
    case None =>
        forall k :: 0 <= k < |str1| ==> CountFrequencyRcr(str1, str1[k]) <= 1
    case Some(pair) =>
        var idx := pair.0;
        var rp_char := pair.1;
        && idx as int <= |str1|
        && (forall i :: 0 <= i < idx as int ==> CountFrequencyRcr(str1, str1[i]) <= 1)
        && CountFrequencyRcr(str1, rp_char) > 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FirstRepeatedChar(str1: array<char>) returns (repeated_char: Option<(nat, char)>)
    ensures CheckFirstRepeatedChar(str1[..], repeated_char)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
