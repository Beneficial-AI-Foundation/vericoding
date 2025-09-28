// <vc-preamble>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)

  ensures ValidBitString(t)

  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): [add lemma for Str2Int expansion property] */
lemma Str2Int_Append_vs_Recursive(s: string, c: char)
  requires ValidBitString(s)
  requires c == '0' || c == '1'
  ensures ValidBitString(s + [c])
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

/* helper modified by LLM (iteration 10): [re-implemented Str2Int_method as recursive to fix verification] */
method Str2Int_method(s: string) returns (n: nat)
  requires ValidBitString(s)
  ensures n == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    n := 0;
  } else {
    var prefix_val := Str2Int_method(s[..|s|-1]);
    var last_digit_val := if s[|s|-1] == '1' then 1 else 0;
    n := 2 * prefix_val + last_digit_val;
  }
}

/* helper modified by LLM (iteration 10): [added lemma call to aid proof in Int2Str] */
method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures |s| > 0
  ensures |s| > 1 ==> s[0] != '0'
  ensures Str2Int(s) == n
  decreases n
{
  if n == 0 {
    s := "0";
  } else {
    var prefix := Int2Str(n / 2);
    var suffix := if n % 2 == 1 then "1" else "0";
    if prefix == "0" {
      s := suffix;
    } else {
      Str2Int_Append_vs_Recursive(prefix, suffix[0]);
      s := prefix + suffix;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): [no changes needed, logic is correct with fixed helpers] */
  var n1 := Str2Int_method(s1);
  var n2 := Str2Int_method(s2);
  res := Int2Str(n1 + n2);
}
// </vc-code>
