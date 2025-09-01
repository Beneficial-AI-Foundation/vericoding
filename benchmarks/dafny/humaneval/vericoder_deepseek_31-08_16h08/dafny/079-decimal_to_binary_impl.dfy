type stringBin = s: string |
  |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
  forall i | 0 <= i < |s| :: s[i] in "01"
  witness "1"

// <vc-helpers>
lemma binary_to_decimal_concat(s1: stringBin, s2: stringBin)
  ensures binary_to_decimal(s1 + s2) == binary_to_decimal(s1) * (if |s2| > 0 then pow2(|s2|) else 1) + binary_to_decimal(s2)
  decreases |s1|
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    var s1_prefix_str := s1[..|s1|-1];
    var s1_last_str := s1[|s1|-1..];
    
    assert |s1_prefix_str| > 0 || |s1_prefix_str| == 0;
    assert |s1_last_str| == 1;
    assert s1_last_str[0] in ['0', '1'];
    
    var s1_prefix: stringBin;
    if |s1_prefix_str| > 0 && (|s1_prefix_str| == 1 || s1_prefix_str[0] != '0') then {
      s1_prefix := s1_prefix_str;
    } else {
      s1_prefix := "1";
    }
    
    var s1_last: stringBin := s1_last_str;
    
    binary_to_decimal_concat(s1_prefix, s1_last + s2);
    calc {
      binary_to_decimal(s1 + s2);
      ==
      binary_to_decimal(s1_prefix_str + (s1_last_str + s2));
      ==
      binary_to_decimal(s1_prefix) * pow2(|s1_last_str + s2|) + binary_to_decimal(s1_last + s2);
      ==
      binary_to_decimal(s1_prefix) * pow2(|s1_last| + |s2|) + binary_to_decimal(s1_last + s2);
      ==
      binary_to_decimal(s1_prefix) * pow2(1 + |s2|) + binary_to_decimal(s1_last + s2);
      ==
      binary_to_decimal(s1_prefix) * 2 * pow2(|s2|) + (binary_to_decimal(s1_last) * pow2(|s2|) + binary_to_decimal(s2));
      ==
      (binary_to_decimal(s1_prefix) * 2 + binary_to_decimal(s1_last)) * pow2(|s2|) + binary_to_decimal(s2);
      ==
      binary_to_decimal(s1) * pow2(|s2|) + binary_to_decimal(s2);
    }
  }
}

lemma binary_decomposition_lemma(n: nat)
  ensures binary_to_decimal(decimal_to_binary_helper(n / 2)) * 2 + binary_to_decimal(decimal_to_binary_helper(n % 2)) == n
  decreases n
{
  if n >= 2 {
    binary_decomposition_lemma(n / 2);
    binary_decomposition_lemma(n % 2);
  }
}

function pow2(exp: nat): nat
  decreases exp
{
  if exp == 0 then 1
  else 2 * pow2(exp - 1)
}

lemma pow2_property(exp: nat)
  ensures pow2(exp) >= 1
{
  if exp > 0 {
    pow2_property(exp - 1);
  }
}

lemma pow2_add(a: nat, b: nat)
  ensures pow2(a + b) == pow2(a) * pow2(b)
{
  if a > 0 {
    pow2_add(a - 1, b);
  }
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
  var inner := decimal_to_binary_helper(n);
  if |inner| == 0 {
    inner := "0";
  }
  s := "db" + inner + "db";
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