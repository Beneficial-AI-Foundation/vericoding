type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
function string_concat(s1: string, s2: string): string
{
  s1 + s2
}

lemma string_length_concat(s1: string, s2: string)
  ensures |string_concat(s1, s2)| == |s1| + |s2|
{
}

lemma string_prefix_suffix(s: string, prefix: string, suffix: string)
  requires |s| == |prefix| + |suffix|
  requires s[..|prefix|] == prefix
  requires s[|prefix|..] == suffix
  ensures s == prefix + suffix
{
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
  var binary := decimal_to_binary_helper(n);
  var result := "db" + binary + "db";
  string_length_concat("db", binary);
  string_length_concat(binary, "db");
  string_length_concat("db" + binary, "db");
  assert |result| == 2 + |binary| + 2;
  assert result[..2] == "db";
  assert result[|result| - 2..] == "db";
  assert result[2..|result| - 2] == binary;
  return result;
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