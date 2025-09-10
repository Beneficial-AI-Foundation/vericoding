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
function LuckyNumberToInt(n: string): int
  requires ValidLuckyNumber(n)
  ensures LuckyNumberToInt(n) == binaryToInt(convertToBinary(n))
{
  if |n| == 0 then 0
  else if n[0] == '4' then 
    LuckyNumberToInt(n[1..])
  else 
    pow2(|n|-1) + LuckyNumberToInt(n[1..])
}

lemma LuckyNumberToInt_equal_binaryToInt_convertToBinary(n: string)
  requires ValidLuckyNumber(n)
  ensures LuckyNumberToInt(n) == binaryToInt(convertToBinary(n))
{
  if |n| == 0 {
    assert LuckyNumberToInt(n) == 0;
    assert convertToBinary(n) == "";
    assert binaryToInt(convertToBinary(n)) == 0;
  } else {
    // If n[1..] is empty string, then it is not a valid lucky number.
    // The recursive call would fail.
    // So we need to ensure that n[1..] is valid lucky number string.
    if |n| > 1 {
      LuckyNumberToInt_equal_binaryToInt_convertToBinary(n[1..]);
    }

    if n[0] == '4' {
      assert n[0] == '4';
      assert convertToBinary(n)[0] == '0';
      assert binaryToInt(convertToBinary(n)) == binaryToInt(convertToBinary(n[1..]));
      assert LuckyNumberToInt(n) == LuckyNumberToInt(n[1..]);
      assert LuckyNumberToInt(n) == binaryToInt(convertToBinary(n));
      
    } else {
      assert n[0] == '7';
      assert convertToBinary(n)[0] == '1';
      assert binaryToInt(convertToBinary(n)) == pow2(|n|-1) + binaryToInt(convertToBinary(n[1..]));
      assert LuckyNumberToInt(n) == pow2(|n|-1) + LuckyNumberToInt(n[1..]);
      assert LuckyNumberToInt(n) == binaryToInt(convertToBinary(n));
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: string) returns (result: int)
    requires ValidLuckyNumber(n)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
    LuckyNumberToInt_equal_binaryToInt_convertToBinary(n);
    result := 2 * (pow2(|n|-1) - 1) + LuckyNumberToInt(n) + 1;
}
// </vc-code>

