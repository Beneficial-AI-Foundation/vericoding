```vc-helpers
function method BitsToNat(s: string): nat
  requires ValidBitString(s)
  decreases |s|
{
  if |s| == 0 then 0 else 2 * BitsToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function method NatToStr(n: nat): string
  decreases n
{
  if n == 0 then "" else NatToStr(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma BitsToNat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures BitsToNat(s) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    BitsToNat_eq_Str2Int(s[0..|s|-1]);
    // By definitions both follow same recurrence, so equal
  }
}

lemma NatToStr_correct(n: nat)
  ensures ValidBitString(NatToStr(n)) && Str2Int(NatToStr(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    NatToStr_correct(n / 2);
    // Str2Int(NatToStr(n)) = 2*Str2Int(NatToStr(n/2)) + (n%2)
    // by inductive hypothesis Str2Int(NatToStr(n/2)) == n/2, so equals n
  }
}

lemma Exp_int_add(x: nat, u: nat, v: nat)
  ensures Exp_int(x, u + v) == Exp_int(x, u) * Exp_int(x, v)
  decreases v
{
  if v == 0 {
  } else {
    Exp_int_add(x, u, v - 1);
    // Exp_int(x, u+v) = x * Exp_int(x, u+v-1)
    // by IH Exp_int(x, u+v-1) = Exp_int(x,u)*Exp_int(x,v-1)
    // so Exp_int(x, u+v) = Exp_int(x,u) * (x * Exp_int(x,v-1)) = Exp_int(x,u)*Exp_int(x,v)
  }
}

