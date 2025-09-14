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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Str2IntMod(s: string, m: nat): nat
  requires ValidBitString(s)
  requires m > 0
  decreases s
{
  if |s| == 0 then 0
  else (2 * Str2IntMod(s[0..|s|-1], m) + (if s[|s|-1] == '1' then 1 else 0)) % m
}

ghost function Exp_int_Mod(x: nat, y: nat, m: nat): nat
  requires m > 0
  decreases y
{
  if y == 0 then 1
  else (x * Exp_int_Mod(x, y - 1, m)) % m
}

function Int2Str(n: nat): string
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

lemma Exp_int_Mod_identity(x: nat, y: nat, m: nat)
  requires m > 0
  ensures Exp_int(x, y) % m == Exp_int_Mod(x, y, m)
{
  if y == 0 {
    assert Exp_int(x,0) % m == 1 % m;
    assert Exp_int_Mod(x,0,m) == 1;
  } else {
    calc {
      Exp_int(x,y) % m;
      (x * Exp_int(x, y-1)) % m;
      ((x % m) * (Exp_int(x, y-1) % m)) % m;
      ((x % m) * Exp_int_Mod(x, y-1, m)) % m;
    }
  }
}

lemma Exp_int_Mod_mult_distributes(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{}

lemma Exp_int_Div2(x: nat, y: nat)
  requires y >= 2
  ensures Exp_int(x, y) == Exp_int(x*x, y/2) * (if y % 2 == 1 then x else 1)
{
  if y % 2 == 1 {
    assert y/2 + y/2 + 1 == y;
    assert Exp_int(x*x, y/2) == Exp_int(x, 2*(y/2));
    calc {
      Exp_int(x,y);
      Exp_int(x, 2*(y/2) + 1);
      x * Exp_int(x, 2*(y/2));
      x * Exp_int(x*x, y/2);
    }
  } else {
    assert y/2 + y/2 == y;
    assert Exp_int(x*x, y/2) == Exp_int(x, 2*(y/2));
    calc {
      Exp_int(x,y);
      Exp_int(x, 2*(y/2));
      Exp_int(x*x, y/2);
    }
  }
}

lemma Exp_int_pow2(b: nat, k: nat)
  ensures Exp_int(b, k) == Exp_int(b*b, k/2) * (if k % 2 == 1 then b else 1)
{
  if k == 0 {}
  else if k == 1 {
    assert Exp_int(b, 1) == b;
    assert Exp_int(b*b, 0) == 1;
    assert (if 1 % 2 == 1 then b else 1) == b;
    assert b == 1 * b;
  } else {
    Exp_int_Div2(b, k);
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
    var x_int := Str2Int(sx);
    var y_int := Str2Int(sy);
    var z_int := Str2Int(sz);
    var acc_val_temp: nat := 1; // Non-ghost variable
    var acc_val: ghost nat := 1; // Ghost variable for invariant
    var base_val: ghost nat := x_int % z_int;
    var base_val_temp: nat := x_int % z_int; // Non-ghost variable

    var k: nat := y_int;
    while k > 0
        invariant z_int > 1
        invariant 0 <= acc_val_temp < z_int
        invariant 0 <= base_val_temp < z_int
        invariant acc_val == acc_val_temp
        invariant base_val == base_val_temp
        invariant (Exp_int(x_int, y_int) % z_int) == (acc_val * Exp_int(base_val, k)) % z_int
        decreases k
    {
        if k % 2 == 1 {
            Exp_int_Mod_mult_distributes(acc_val, base_val, z_int);
            acc_val_temp := (acc_val_temp * base_val_temp) % z_int;
            acc_val := (acc_val * base_val) % z_int;
        }
        Exp_int_Mod_mult_distributes(base_val, base_val, z_int);
        Exp_int_pow2(base_val, k);
        base_val_temp := (base_val_temp * base_val_temp) % z_int;
        base_val := (base_val * base_val) % z_int;
        k := k / 2;
    }
    res := Int2Str(acc_val_temp);
}
// </vc-code>

