type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
function decimal_to_binary_correct(n: nat): stringBin 
  ensures binary_to_decimal(decimal_to_binary_correct(n)) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else decimal_to_binary_correct(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma decimal_to_binary_correct_lemma(n: nat)
  ensures binary_to_decimal(decimal_to_binary_correct(n)) == n
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def decimal_to_binary(decimal: nat) -> string
You will be given a number in decimal form and your task is to convert it to binary format. The function should return a string, with each character representing a binary number. Each character in the string will be '0' or '1'.
*/
// </vc-description>

// <vc-spec>
method decimal_to_binary(decimal: nat) returns (result: stringBin)
  ensures binary_to_decimal(result) == decimal
// </vc-spec>
// <vc-code>
{
  result := decimal_to_binary_correct(decimal);
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