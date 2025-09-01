type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
lemma decimal_to_binary_helper_properties(n: nat)
  ensures |decimal_to_binary_helper(n)| >= 1
  ensures decimal_to_binary_helper(n) in stringBin
{
  match n
    case 0 => {}
    case 1 => {}
    case _ => 
      decimal_to_binary_helper_properties(n / 2);
      decimal_to_binary_helper_properties(n % 2);
}

lemma string_concatenation_length(s1: string, s2: string, s3: string)
  ensures |s1 + s2 + s3| == |s1| + |s2| + |s3|
{
}

lemma string_slicing_properties(s: string)
  requires |s| >= 4
  ensures s[..2] + s[2..|s| - 2] + s[|s| - 2..] == s
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
  decimal_to_binary_helper_properties(n);
  var binary_part := decimal_to_binary_helper(n);
  s := "db" + binary_part + "db";
  string_concatenation_length("db", binary_part, "db");
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