type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
function decimal_to_binary_helper_079(n: nat): stringBin
  ensures binary_to_decimal_079(decimal_to_binary_helper_079(n)) == n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else
    decimal_to_binary_helper_079(n / 2) + decimal_to_binary_helper_079(n % 2)
}

function binary_to_decimal_079(s: stringBin): nat
  decreases |s|
{
  if |s| == 1 then
    if s[0] == '0' then 0 else 1
  else
    binary_to_decimal_079(s[..|s|-1])*2 + binary_to_decimal_079(s[|s|-1..|s|])
}
// </vc-helpers>

// <vc-spec>
method decimal_to_binary(n: nat) returns (s: string)
  // post-conditions-start
  ensures |s| == |decimal_to_binary_helper(n)| + 4
  ensures s[..2] == "db"
  ensures s[|s| - 2..] == "db"
  ensures s[2..|s| - 2] == decimal_to_binary_helper(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var helper_s := decimal_to_binary_helper_079(n);
  s := "db" + helper_s + "db";
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