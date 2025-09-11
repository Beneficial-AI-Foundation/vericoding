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
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2Nat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function Nat2Str(n: nat): string
  ensures ValidBitString(Nat2Str(n))
  ensures Str2Nat(Nat2Str(n)) == n
  decreases n
{
  if n == 0 then "" else Nat2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

lemma Str2Nat_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2Nat(s)
  decreases s
{
  if |s| == 0 {
  } else {
    Str2Nat_eq_Str2Int(s[0..|s|-1]);
  }
}

lemma Nat2Str_str2nat(n: nat)
  ensures Str2Nat(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    Nat2Str_str2nat(n / 2);
  }
}

method PowMod(a: nat, y: nat, m: nat) returns (r: nat)
  requires m > 0
  ensures r == Exp_int(a, y) % m
  decreases y
{
  if y == 0 {
    r := 1 % m;
    return;
  }
  var t := PowMod(a, y - 1, m);
  r := (t * a) % m;
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
  var a := Str2Nat(sx);
  var y := Str2Nat(sy);
  var m := Str2Nat(sz);
  assert m > 1;
  var res_int := PowMod(a, y, m);
  var r := Nat2Str(res_int);
  ghost {
    Str2Nat_eq_Str2Int(sx);
    Str2Nat_eq_Str2Int(sy);
    Str2Nat_eq_Str2Int(sz);
    Nat2Str_str2nat(res_int);
    Str2Nat_eq_Str2Int(Nat2Str(res_int));
  }
  return r;
}
// </vc-code>

