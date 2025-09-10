predicate ValidBinaryString(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

function countZeros(s: string): int
    ensures countZeros(s) >= 0
    ensures countZeros(s) <= |s|
{
    if |s| == 0 then 0
    else if s[0] == '0' then 1 + countZeros(s[1..])
    else countZeros(s[1..])
}

function countOnes(s: string): int
    ensures countOnes(s) >= 0
    ensures countOnes(s) <= |s|
{
    if |s| == 0 then 0
    else if s[0] == '1' then 1 + countOnes(s[1..])
    else countOnes(s[1..])
}

function longestNonDecreasingSubseqLengthComplete(s: string): int
    ensures longestNonDecreasingSubseqLengthComplete(s) >= (if |s| == 0 then 0 else 1)
    ensures longestNonDecreasingSubseqLengthComplete(s) <= |s|
{
    if |s| == 0 then 0
    else if |s| == 1 then 1
    else 
        var countOnes := countOnes(s);
        var countZeros := |s| - countOnes;
        if countZeros == 0 then countOnes
        else if countOnes == 0 then 1
        else countZeros + countOnes
}

function longestNonDecreasingSubseqLength(s: string, l: int, r: int): int
    requires 0 <= l <= r < |s|
    ensures longestNonDecreasingSubseqLength(s, l, r) >= 1
    ensures longestNonDecreasingSubseqLength(s, l, r) <= r - l + 1
{
    var sub := s[l..r+1];
    longestNonDecreasingSubseqLengthComplete(sub)
}

predicate BasicValidSolution(s: string, t: string)
{
    && |s| == |t|
    && ValidBinaryString(s)
    && ValidBinaryString(t)
    && (forall i :: 0 <= i < |s| ==> s[i] == '0' ==> t[i] == '0')
    && (forall i :: 0 <= i < |s| ==> t[i] == '1' ==> s[i] == '1')
}

// <vc-helpers>
predicate PrefixValidSolution(s: string, t: string, k: int)
    requires 0 <= k <= |s|
{
    match k
    case 0 => true
    case _ =>
        && ValidBinaryString(t[..k])
        && (forall i :: 0 <= i < k ==> s[i] == '0' ==> t[i] == '0')
        && (forall i :: 0 <= i < k ==> t[i] == '1' ==> s[i] == '1')
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidBinaryString(s)
    ensures BasicValidSolution(s, result)
// </vc-spec>
// <vc-code>
{
    var charArray := new char[|s|];
    var t := "";

    var k := 0;
    while k < |s|
        invariant 0 <= k <= |s|
        invariant |charArray| == |s|
        invariant t == String.FromCharArray(charArray[..k])
        invariant ValidBinaryString(s)
        invariant PrefixValidSolution(s, t, k)
    {
        if s[k] == '0' {
            charArray[k] := '0';
        } else { // s[k] == '1'
            charArray[k] := '1';
        }
        t := String.FromCharArray(charArray[..k+1]);
        k := k + 1;
    }

    result := String.FromCharArray(charArray);
}
// </vc-code>

