ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

// <vc-helpers>
// Helper to parse a bitstring into a nat (executable)
method ParseBitString(s: string) returns (v: nat)
  requires ValidBitString(s)
  ensures v == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    v := 0;
    return;
  }
  var prefix := s[0..|s|-1];
  var bit := if s[|s|-1] == '1' then 1 else 0;
  var pval := ParseBitString(prefix);
  v := 2 * pval + bit;
}

// Lemma: appending a single bit to a bitstring corresponds to doubling + bit
lemma Str2Int_Append(s: string, b: bool)
  requires ValidBitString(s)
  ensures Str2Int(s + (if b then "1" else "0")) == 2 * Str2Int(s) + (if b then 1 else 0)
  decreases s
{
  var c := if b then "1" else "0";
  // facts about concatenation
  assert |s + c| == |s| + 1;
  assert (s + c)[0..|s + c| - 1] == s;
  assert (s + c)[|s + c| - 1] == c[0];
  // unfold definition of Str2Int on s + c
  assert Str2Int(s + c) == 2 * Str2Int((s + c)[0..|s + c| - 1]) + (if (s + c)[|s + c| - 1] == '1' then 1 else 0);
  // substitute the substring and last char facts
  assert Str2Int((s + c)[0..|s + c| - 1]) == Str2Int(s);
  assert (if (s + c)[|s + c| - 1] == '1' then 1 else 0) == (if b then 1 else 0);
  assert Str2Int(s + c) == 2 * Str2Int(s) + (if b then 1 else 0);
}

// Convert a natural number to a bitstring (executable)
method IntToStr(x: nat) returns (s: string)
  ensures ValidBitString(s) && Str2Int(s) == x
  decreases x
{
  if x == 0 {
    s := "";
    return;
  }
  var q := x / 2;
  var r := x % 2;
  var prefix := IntToStr(q);
  if r == 1 {
    // prefix is ValidBitString by postcondition of recursive call
    // use lemma to prove Str2Int(prefix + "1") == 2*Str2Int(prefix) + 1 == x
    Str2Int_Append(prefix, true);
    s := prefix + "1";
  } else {
    Str2Int_Append(prefix, false);
    s := prefix + "0";
  }
}

// Executable powering routine that matches the ghost Exp_int definition
method Pow_nat(x: nat, y: nat) returns (p: nat)
  ensures p == Exp_int(x, y)
  decreases y
{
  if y == 0 {
    p := 1;
    return;
  }
  var q := Pow_nat(x, y - 1);
  p := x * q;
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  //requires y < Exp_int(2,n+1)
  requires |sy| > 0 && Str2Int(sz) > 1 //&& n > 0
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  var a := ParseBitString(sx);
  var b := ParseBitString(sy);
  var m := ParseBitString(sz);
  var p := Pow_nat(a, b);
  var v := p % m;
  res := IntToStr(v);
}
// </vc-code>

