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

lemma Nat2Str_inv(n: nat)
  ensures Str2Int(Nat2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else {
    Nat2Str_inv(n / 2);
  }
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
  // Use lemma to relate Str2Nat and Str2Int for sz so we can prove modulus divisor is non-zero.
  Str2Nat_eq_Str2Int(sz);
  var m := Str2Nat(sz);
  assert m > 1;

  if |sy| == 1 {
    if sy[0] == '1' {
      return Nat2Str(Str2Nat(sx) % m);
    } else {
      return Nat2Str(1 % m);
    }
  } else {
    var sxmod := Str2Nat(sx) % m;
    var sy0 := sy[0..|sy|-1];
    var bit := sy[|sy|-1];
    var half := ModExp(sx, sy0, sz);
    var halfv := Str2Nat(half);
    var t := (halfv * halfv) % m;
    var res_int := if bit == '1' then (t * sxmod) % m else t;
    return Nat2Str(res_int);
  }
}
// </vc-code>

