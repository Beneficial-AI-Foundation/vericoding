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

lemma Exp_add(x: nat, n: nat, m: nat)
  ensures Exp_int(x, n + m) == Exp_int(x, n) * Exp_int(x, m)
  decreases m
{
  if m == 0 {
    // Exp_int(x, n + 0) == Exp_int(x,n) and Exp_int(x,0) == 1
  } else {
    Exp_add(x, n, m - 1);
    // Exp_int(x, n + m) == x * Exp_int(x, n + m - 1)
    // by induction hypothesis Exp_int(x, n + m - 1) == Exp_int(x,n) * Exp_int(x, m - 1)
    // so Exp_int(x, n + m) == x * (Exp_int(x,n) * Exp_int(x, m - 1)) == Exp_int(x,n) * Exp_int(x, m)
  }
}

lemma Str2Nat_decomp(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Nat(s) == 2 * Str2Nat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
  decreases s
{
  // direct from definition
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m * b % m) % m == (a * b) % m
{
  var q1 := a / m;
  var r1 := a % m;
  var q2 := b / m;
  var r2 := b % m;
  assert a == m * q1 + r1;
  assert b == m * q2 + r2;
  // (m*q1 + r1)*(m*q2 + r2) = m*(m*q1*q2 + q1*r2 + q2*r1) + r1*r2
  assert a * b == m * (m * q1 * q2 + q1 * r2 + q2 * r1) + r1 * r2;
  // therefore (a*b) % m == (r1*r2) % m
  assert (a * b) % m == (r1 * r2) % m;
  assert r1 == a % m;
  assert r2 == b % m;
  assert r1 * r2 == (a % m) * (b % m);
  assert (r1 * r2) % m == ((a % m) * (b % m)) % m;
}

lemma ModExp_step(a: nat, m: nat, y: nat, k: nat, halfv: nat)
  requires m > 0
  requires k == 0 || k == 1
  requires halfv == Exp_int(a, y) % m
  ensures (if k == 1 then ((halfv * halfv) % m * (a % m)) % m else (halfv * halfv) % m) == Exp_int(a, 2 * y + k) % m
  decreases y
{
  // first relate (halfv*halfv)%m to (Exp_int(a,y)*Exp_int(a,y))%m
  ModMul(halfv, halfv, m);
  // halfv == Exp_int(a,y) % m
  // so (halfv*halfv)%m == (Exp_int(a,y) * Exp_int(a,y)) % m
  if k == 0 {
    // now Exp_int(a, 2*y + 0) == Exp_int(a, y + y) == Exp_int(a,y) * Exp_int(a,y)
    Exp_add(a, y, y);
    // finish by equality of mods
    // (Exp_int(a,y) * Exp_int(a,y)) % m == Exp_int(a, 2*y) % m
  } else {
    // k == 1
    // need two ModMul steps:
    // (halfv*halfv)%m == (Exp_int(a,y)*Exp_int(a,y))%m
    // then ((halfv*halfv)%m * (a%m))%m == (Exp_int(a,y)*Exp_int(a,y) * a) % m
    ModMul(Exp_int(a, y) * Exp_int(a, y), a, m);
    // Exp_int(a, 2*y + 1) == Exp_int(a, 2*y) * a
    Exp_add(a, y, y);
    // thus concluded
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
  Str2Nat_eq_Str2Int(sx);
  Str2Nat_eq_Str2Int(sz);
  var m := Str2Nat(sz);
  assert m > 1;

  if |sy| == 1 {
    if sy[0] == '1' {
      var n := Str2Nat(sx) % m;
      Nat2Str_str2nat(n);
      var r := Nat2Str(n);
      Str2Nat_eq_Str2Int(r);
      return r;
    } else {
      var n := 1 % m;
      Nat2Str_str2nat(n);
      var r := Nat2Str(n);
      Str2Nat_eq_Str2Int(r);
      return r;
    }
  } else {
    var sxmod := Str2Nat(sx) % m;
    var sy0 := sy[0..|sy|-1];
    var bit := sy[|sy|-1];
    var half := ModExp(sx, sy0, sz);
    Str2Nat_eq_Str2Int(half);
    var halfv := Str2Nat(half);
    // by recursive call: Str2Int(half) == Exp_int(Str2Int(sx), Str2Int(sy0)) % Str2Int(sz)
    // convert to Str2Nat domain
    Str2Nat_eq_Str2Int(sy0);
    Str2Nat_eq_Str2Int(sx);
    // get numeric values
    var a := Str2Nat(sx);
    var y0 := Str2Nat(sy0);
    // From recursive call we have:
    // Str2Int(half) == Exp_int(Str2Int(sx), Str2Int(sy0)) % Str2Int(sz)
    // Using Str2Nat_eq_Str2Int(half) and the others, deduce:
    assert halfv == Exp_int(a, y0) % m;

    var t := (halfv * halfv) % m;
    var res_int := if bit == '1' then (t * sxmod) % m else t;

    // relate bit to numeric k
    var k := if bit == '1' then 1 else 0;
    Str2Nat_decomp(sy);
    // Str2Nat(sy) == 2*y0 + k
    assert Str2Nat(sy) == 2 * y0 + k;

    // use lemma to relate modular combination to exponent
    ModExp_step(a, m, y0, k, halfv);
    if k == 1 {
      assert res_int == Exp_int(a, 2 * y0 + 1) % m;
    } else {
      assert res_int == Exp_int(a, 2 * y0 + 0) % m;
    }

    // res_int == Exp_int(a, Str2Nat(sy)) % m
    assert res_int == Exp_int(a, Str2Nat(sy)) % m;

    // convert result integer to string
    Nat2Str_str2nat(res_int);
    var r := Nat2Str(res_int);
    Str2Nat_eq_Str2Int(r);
    // finally Str2Int(r) == res_int and Str2Int(sz) == m by earlier lemma
    return r;
  }
}
// </vc-code>

