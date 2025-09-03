ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function method NatToBin(n: nat): string
  ensures ValidBitString(NatToBin(n))
  ensures Str2Int(NatToBin(n)) == n
  decreases n
{
  if n == 0 then "" else
    var t := NatToBin(n / 2);
    if n % 2 == 1 then t + "1" else t + "0"
}

lemma Exp_int_mul(x: nat, p: nat, q: nat)
  ensures Exp_int(x, p) * Exp_int(x, q) == Exp_int(x, p + q)
  decreases q
{
  if q == 0 {
    // Exp_int(x,0) == 1, so left = Exp_int(x,p) * 1 == Exp_int(x,p) == Exp_int(x,p+0)
  } else {
    Exp_int_mul(x, p, q - 1);
    // Exp_int(x,q) = x * Exp_int(x,q-1)
    // so Exp_int(x,p) * Exp_int(x,q) == Exp_int(x,p) * (x * Exp_int(x,q-1))
    //                         == x * (Exp_int(x,p) * Exp_int(x,q-1))
    // by IH Exp_int(x,p) * Exp_int(x,q-1) == Exp_int(x, p + q - 1)
    // so equals x * Exp_int(x, p + q - 1) == Exp_int(x, p + q)
  }
}

lemma Exp2_succ(i: nat)
  ensures Exp_int(2, i + 1) == 2 * Exp_int(2, i)
  decreases i
{
  if i == 0 {
    // Exp_int(2,1) == 2 and Exp_int(2,0) == 1
  } else {
    Exp2_succ(i - 1);
    // follows from definition of Exp_int
  }
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var m := Str2Int(sz);
  if Str2Int(sy) == 0 {
    // x^0 mod m
    res := NatToBin(1 % m);
    return;
  }
  var x := Str2Int(sx) % m;
  var acc := x;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant acc == Exp_int(Str2Int(sx), Exp_int(2, i)) % m
  {
    acc := (acc * acc) % m;
    // Show the invariant for the next i: uses Exp_int_mul and Exp2_succ
    i := i + 1;
  }
  res := NatToBin(acc);
}
// </vc-code>

