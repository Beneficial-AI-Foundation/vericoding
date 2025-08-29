type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
function BinaryToDecimal(s: stringBin): nat
  decreases |s|
{
  if |s| == 1 then
    match s[0]
    case '0' => 0
    case '1' => 1
  else
    BinaryToDecimal(s[..|s|-1]) * 2 + BinaryToDecimal(s[|s|-1..|s|])
}

lemma BinaryConversionCorrect(n: nat)
  ensures BinaryToDecimal(DecimalToBinaryHelper(n)) == n
{
  if n == 0 || n == 1 {
    assert DecimalToBinaryHelper(n) == if n == 0 then "0" else "1";
    assert BinaryToDecimal(DecimalToBinaryHelper(n)) == n;
  } else {
    var bin := DecimalToBinaryHelper(n);
    var bin_div := DecimalToBinaryHelper(n / 2);
    var bin_mod := DecimalToBinaryHelper(n % 2);
    assert bin == bin_div + bin_mod;
    BinaryConversionCorrect(n / 2);
    BinaryConversionCorrect(n % 2);
    assert BinaryToDecimal(bin_div) == n / 2;
    assert BinaryToDecimal(bin_mod) == n % 2;
    assert BinaryToDecimal(bin) == BinaryToDecimal(bin_div) * 2 + BinaryToDecimal(bin_mod);
    assert BinaryToDecimal(bin) == (n / 2) * 2 + (n % 2);
    assert BinaryToDecimal(bin) == n;
  }
}

function DecimalToBinaryHelper(n: nat): stringBin
  ensures BinaryToDecimal(DecimalToBinaryHelper(n)) == n
{
  match n
    case 0 => "0"
    case 1 => "1"
    case _ => DecimalToBinaryHelper(n / 2) + DecimalToBinaryHelper(n % 2)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def decimal_to_binary(decimal: nat) -> string
You will be given a number in decimal form and your task is to convert it to binary format. The function should return a string, with each character representing a binary number. Each character in the string will be '0' or '1'.
*/
// </vc-description>

// <vc-spec>
method decimal_to_binary(decimal: nat) returns (binary: stringBin)
  ensures BinaryToDecimal(binary) == decimal
// </vc-spec>
// <vc-code>
{
  binary := DecimalToBinaryHelper(decimal);
}
// </vc-code>

function decimal_to_binary_helper(n: nat): stringBin 
  // post-conditions-start
  ensures binary_to_decimal(decimal_to_binary_helper(n)) == n
  // post-conditions-end
{
  // impl-start
  match n
    case 0 => "0" case 1 => "1"
    case _ => decimal_to_binary_helper(n / 2) + decimal_to_binary_helper(n % 2)
  // impl-end
}
// pure-end
function binary_to_decimal(s: stringBin): nat
  decreases |s|
{
  if |s| == 1 then
    match s[0]
    case '0' => 0 case '1' => 1
  else
    binary_to_decimal(s[..|s|-1])*2 + binary_to_decimal(s[|s|-1..|s|])
}
// pure-end