predicate ValidLuckyNumber(n: string)
{
    |n| > 0 && forall i :: 0 <= i < |n| ==> n[i] == '4' || n[i] == '7'
}

function convertToBinary(n: string): string
    requires forall i :: 0 <= i < |n| ==> n[i] == '4' || n[i] == '7'
    ensures |convertToBinary(n)| == |n|
    ensures forall i :: 0 <= i < |n| ==> (n[i] == '4' ==> convertToBinary(n)[i] == '0') && (n[i] == '7' ==> convertToBinary(n)[i] == '1')
{
    if |n| == 0 then ""
    else if n[0] == '4' then "0" + convertToBinary(n[1..])
    else "1" + convertToBinary(n[1..])
}

function pow2(n: int): int
    requires n >= 0
    ensures pow2(n) > 0
{
    if n == 0 then 1
    else 2 * pow2(n - 1)
}

function binaryToInt(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
    ensures binaryToInt(s) >= 0
{
    if |s| == 0 then 0
    else if s[0] == '1' then pow2(|s|-1) + binaryToInt(s[1..])
    else binaryToInt(s[1..])
}

predicate ValidResult(n: string, result: int)
    requires ValidLuckyNumber(n)
{
    result > 0 && result == 2 * (pow2(|n|-1) - 1) + binaryToInt(convertToBinary(n)) + 1
}

// <vc-helpers>
lemma BinaryConversionPreservesLength(n: string)
    requires forall i :: 0 <= i < |n| ==> n[i] == '4' || n[i] == '7'
    ensures |convertToBinary(n)| == |n|
{
}

lemma BinaryConversionCorrect(n: string)
    requires forall i :: 0 <= i < |n| ==> n[i] == '4' || n[i] == '7'
    ensures forall i :: 0 <= i < |n| ==> (n[i] == '4' ==> convertToBinary(n)[i] == '0') && (n[i] == '7' ==> convertToBinary(n)[i] == '1')
{
}

lemma ConvertedBinaryIsValid(n: string)
    requires forall i :: 0 <= i < |n| ==> n[i] == '4' || n[i] == '7'
    ensures forall i :: 0 <= i < |convertToBinary(n)| ==> convertToBinary(n)[i] == '0' || convertToBinary(n)[i] == '1'
{
    BinaryConversionCorrect(n);
}

lemma Pow2Positive(n: int)
    requires n >= 0
    ensures pow2(n) > 0
{
}

lemma BinaryToIntNonNegative(s: string)
    requires forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
    ensures binaryToInt(s) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: string) returns (result: int)
    requires ValidLuckyNumber(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    var binary := convertToBinary(n);
    BinaryConversionPreservesLength(n);
    ConvertedBinaryIsValid(n);
    
    var binaryValue := binaryToInt(binary);
    BinaryToIntNonNegative(binary);
    
    if |n| == 1 {
        Pow2Positive(0);
        result := 2 * (pow2(0) - 1) + binaryValue + 1;
    } else {
        Pow2Positive(|n| - 1);
        result := 2 * (pow2(|n| - 1) - 1) + binaryValue + 1;
    }
}
// </vc-code>

