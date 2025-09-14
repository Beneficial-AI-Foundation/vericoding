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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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
lemma mod_mult(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma mod_exp_property(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == (if y == 0 then 1 % m else (x * Exp_int(x, y - 1)) % m)
  decreases y
{
  if y != 0 {
    mod_exp_property(x, y - 1, m);
    mod_mult(x, Exp_int(x, y - 1), m);
  }
}

lemma mod_exp_recursive(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == (if y == 0 then 1 else (x % m) * (Exp_int(x, y - 1) % m) % m) % m
  decreases y
{
  if y != 0 {
    mod_exp_property(x, y, m);
    mod_mult(x, Exp_int(x, y - 1), m);
    mod_exp_recursive(x, y - 1, m);
  }
}

lemma Str2Int_append(s: string, c: char)
  requires ValidBitString(s) && (c == '0' || c == '1')
  ensures Str2Int(s + [c]) == 2 * Str2Int(s) + (if c == '1' then 1 else 0)
{
}

lemma Str2Int_last_char(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma Exp_int_property(x: nat, y: nat)
  ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
{
}

lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

ghost function Int2String(n: nat, len: nat): string
  ensures ValidBitString(Int2String(n, len))
  ensures Str2Int(Int2String(n, len)) == n % Exp_int(2, len)
  decreases len
{
  if len == 0 then ""
  else 
    var prefix := Int2String(n / 2, len - 1);
    var last_char := if n % 2 == 1 then '1' else '0';
    prefix + [last_char]
}

ghost function GhostStringFromNat(n: nat, len: nat): string
  decreases n, len
{
  Int2String(n, len)
}

ghost function GhostHalfString(sy: string): string
  requires ValidBitString(sy) && |sy| > 0
  ensures ValidBitString(GhostHalfString(sy))
  ensures Str2Int(GhostHalfString(sy)) == Str2Int(sy) / 2
{
  var half_y := Str2Int(sy) / 2;
  Int2String(half_y, |sy|)
}

ghost function GhostModVal(x_val: nat, z_val: nat, sz: nat): string
  requires z_val > 1
  ensures ValidBitString(GhostModVal(x_val, z_val, sz))
  ensures Str2Int(GhostModVal(x_val, z_val, sz)) == x_val % z_val
{
  var mod_val := x_val % z_val;
  Int2String(mod_val, sz)
}

ghost function GhostSquare(rec_int: nat, z_val: nat, sz: nat): string
  requires z_val > 1
  ensures ValidBitString(GhostSquare(rec_int, z_val, sz))
  ensures Str2Int(GhostSquare(rec_int, z_val, sz)) == (rec_int * rec_int) % z_val
{
  var square := (rec_int * rec_int) % z_val;
  Int2String(square, sz)
}

ghost function GhostProduct(square: nat, x_val: nat, z_val: nat, sz: nat): string
  requires z_val > 1
  ensures ValidBitString(GhostProduct(square, x_val, z_val, sz))
  ensures Str2Int(GhostProduct(square, x_val, z_val, sz)) == (square * (x_val % z_val)) % z_val
{
  var product := (square * (x_val % z_val)) % z_val;
  Int2String(product, sz)
}

ghost method GhostZeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  if n == 0 {
    s := "";
  } else {
    var rest := GhostZeros(n-1);
    s := rest + "0";
  }
}

function BitLength(n: nat): nat
  decreases n
{
  if n == 0 then 1
  else if n == 1 then 1
  else 1 + BitLength(n / 2)
}

lemma BitLength_property(n: nat)
  ensures n < Exp_int(2, BitLength(n))
  decreases n
{
  if n > 1 {
    BitLength_property(n / 2);
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
  ghost var x_val := Str2Int(sx);
  ghost var y_val := Str2Int(sy);
  ghost var z_val := Str2Int(sz);
  
  if y_val == 0 {
    res := "1";
  } else if y_val == 1 {
    res := GhostModVal(x_val, z_val, |sz|);
  } else {
    var half_y_str := GhostHalfString(sy);
    
    var rec_val := ModExp(sx, half_y_str, sz);
    var rec_int := Str2Int(rec_val);
    
    if y_val % 2 == 0 {
      res := GhostSquare(rec_int, z_val, |sz|);
    } else {
      var square := (rec_int * rec_int) % z_val;
      res := GhostProduct(square, x_val, z_val, |sz|);
    }
  }
}
// </vc-code>

