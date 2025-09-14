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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
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

function method NatToStr(n: nat): string
{
  if n == 0 then "0" else
  var s := "";
  var temp := n;
  while temp > 0
    invariant 0 <= temp
    invariant temp <= n
    decreases temp
  {
    s := (if temp % 2 == 0 then "0" else "1") + s;
    temp := temp / 2;
  }
  s
}

function method Mod(a: nat, b: nat): nat
  requires b > 0
{
  a % b
}

lemma NatToStr_Str2Int(s: string)
  requires ValidBitString(s)
  ensures NatToStr(Str2Int(s)) == s
{
  if |s| == 0 {
  } else {
    NatToStr_Str2Int(s[0..|s|-1]);
    assert NatToStr(Str2Int(s)) == NatToStr(2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
    calc == {
      NatToStr(2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
      NatToStr(Str2Int(s[0..|s|-1]) * 2 + (if s[|s|-1] == '1' then 1 else 0));
      { assert NatToStr(Str2Int(s[0..|s|-1])) == s[0..|s|-1]; }
      NatToStr(s[0..|s|-1]) + (if s[|s|-1] == '1' then "1" else "0");
      s[0..|s|-1] + s[|s|-1];
      s;
    }
  }
}

lemma Str2Int_NatToStr(n: nat)
  ensures Str2Int(NatToStr(n)) == n
{
  if n == 0 {
  } else {
    var s := NatToStr(n);
    calc == {
      Str2Int(s);
      Str2Int(NatToStr(n));
      { assert NatToStr(Str2Int(s[0..|s|-1])) == s[0..|s|-1]; }
      Str2Int(NatToStr(Str2Int(s[0..|s|-1])));
      { 
        assert Str2Int(s[0..|s|-1]) < n;
        Str2Int_NatToStr(Str2Int(s[0..|s|-1]));
      }
      Str2Int(s[0..|s|-1]);
      2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
      2 * (n / 2) + (n % 2);
      n;
    }
  }
}

lemma ModExpProperty(x: nat, y: nat, z: nat, r: nat)
  requires z > 0
  requires r == Exp_int(x, y) % z
{
}

lemma Mod_mult_congruence(a: nat, b: nat, c: nat, d: nat, k: nat)
  requires a % k == b % k
  requires c % k == d % k
  ensures (a * c) % k == (b * d) % k
{
  assert (a * c) % k == ((a % k) * (c % k)) % k;
  assert (b * d) % k == ((b % k) * (d % k)) % k;
}

lemma Exp_int_mod_property(x: nat, y: nat, z: nat)
  requires z > 0
  ensures (Exp_int(x % z, y)) % z == Exp_int(x, y) % z
{
  if y == 0 {
  } else {
    Exp_int_mod_property(x, y - 1, z);
    calc == {
      Exp_int(x % z, y) % z;
      (x % z * Exp_int(x % z, y - 1)) % z;
      (x % z * (Exp_int(x, y - 1) % z)) % z;
      { Mod_mult_congruence(x % z, x, Exp_int(x, y - 1) % z, Exp_int(x, y - 1), z); }
      (x * Exp_int(x, y - 1) % z) % z;
      Exp_int(x, y) % z;
    }
  }
}

lemma Exp_int_square_mod_property(x: nat, y: nat, z: nat)
  requires z > 0
  ensures (Exp_int(Exp_int(x, y) % z, 2)) % z == Exp_int(x, 2 * y) % z
{
  calc == {
    Exp_int(Exp_int(x, y) % z, 2) % z;
    ((Exp_int(x, y) % z) * (Exp_int(x, y) % z)) % z;
    (Exp_int(x, y) * Exp_int(x, y)) % z;
    Exp_int(x, 2 * y) % z;
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
  var x := Str2Int(sx);
  var y := Str2Int(sy);
  var z := Str2Int(sz);
  var r := 1;
  
  var y_remaining := y;
  var x_power := x % z;
  
  while y_remaining > 0
    invariant 0 <= y_remaining <= y
    invariant r == Exp_int(x, y - y_remaining) % z
    invariant x_power == Exp_int(x, y - y_remaining) % z
    decreases y_remaining
  {
    if y_remaining % 2 == 1 {
      r := (r * x_power) % z;
      calc == {
        r;
        (r * x_power) % z;
        (Exp_int(x, y - y_remaining) % z * x_power) % z;
        (Exp_int(x, y - y_remaining) % z * Exp_int(x, y - y_remaining) % z) % z;
        { Mod_mult_congruence(Exp_int(x, y - y_remaining), Exp_int(x, y - y_remaining) % z, 
                              Exp_int(x, y - y_remaining), Exp_int(x, y - y_remaining) % z, z); }
        (Exp_int(x, y - y_remaining) * Exp_int(x, y - y_remaining)) % z;
        Exp_int(x, (y - y_remaining) + (y - y_remaining)) % z;
        Exp_int(x, 2*(y - y_remaining)) % z;
        { assert (y - (y_remaining - 1)) == (y - y_remaining) + 1; }
        Exp_int(x, y - (y_remaining - 1)) % z;
      }
    }
    x_power := (x_power * x_power) % z;
    calc == {
      x_power;
      (x_power * x_power) % z;
      (Exp_int(x, y - y_remaining) % z * Exp_int(x, y - y_remaining) % z) % z;
      { Mod_mult_congruence(Exp_int(x, y - y_remaining), Exp_int(x, y - y_remaining) % z,
                            Exp_int(x, y - y_remaining), Exp_int(x, y - y_remaining) % z, z); }
      (Exp_int(x, y - y_remaining) * Exp_int(x, y - y_remaining)) % z;
      Exp_int(x, (y - y_remaining) + (y - y_remaining)) % z;
      Exp_int(x, 2*(y - y_remaining)) % z;
      Exp_int(x, y - y_remaining + y_remaining - y_remaining/2) % z;
      Exp_int(x, y - (y_remaining/2)) % z;
    }
    y_remaining := y_remaining / 2;
  }
  
  calc == {
    r;
    Exp_int(x, y - y_remaining) % z;
    Exp_int(x, y - 0) % z;
    Exp_int(x, y) % z;
  }
  
  res := NatToStr(r);
  NatToStr_Str2Int(res);
  ModExpProperty(x, y, z, r);
}
// </vc-code>

