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

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
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

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Exp_int_Add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert a + b == a;
    assert Exp_int(x, b) == 1;
  } else {
    Exp_int_Add(x, a, b - 1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1));
    assert Exp_int(x, a + (b - 1)) == Exp_int(x, a) * Exp_int(x, b - 1);
    assert Exp_int(x, b) == x * Exp_int(x, b - 1);
  }
}

lemma Exp_int_Mult(x: nat, a: nat, b: nat)
  ensures Exp_int(Exp_int(x, a), b) == Exp_int(x, a * b)
{
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(Exp_int(x, a), 0) == 1;
    assert Exp_int(x, 0) == 1;
  } else {
    Exp_int_Mult(x, a, b - 1);
    assert Exp_int(Exp_int(x, a), b) == Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
    assert Exp_int(Exp_int(x, a), b - 1) == Exp_int(x, a * (b - 1));
    assert a * b == a + a * (b - 1);
    Exp_int_Add(x, a, a * (b - 1));
    assert Exp_int(x, a * b) == Exp_int(x, a) * Exp_int(x, a * (b - 1));
  }
}

lemma ModExpDecomposition(x: nat, q: nat, n: nat, r: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, q * Exp_int(2, n) + r) % z == 
          (Exp_int(Exp_int(x, Exp_int(2, n)), q) * Exp_int(x, r)) % z
{
  var y := q * Exp_int(2, n) + r;
  assert y == q * Exp_int(2, n) + r;
  
  Exp_int_Add(x, q * Exp_int(2, n), r);
  assert Exp_int(x, y) == Exp_int(x, q * Exp_int(2, n)) * Exp_int(x, r);
  
  Exp_int_Mult(x, Exp_int(2, n), q);
  assert Exp_int(x, q * Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n)), q);
  
  assert Exp_int(x, y) == Exp_int(Exp_int(x, Exp_int(2, n)), q) * Exp_int(x, r);
}

lemma PowerOf2Bound(n: nat)
  ensures Exp_int(2, n) > 0
  ensures forall r: nat :: r < Exp_int(2, n) ==> r / Exp_int(2, n) == 0
{
  if n == 0 {
    assert Exp_int(2, 0) == 1;
  } else {
    PowerOf2Bound(n - 1);
    assert Exp_int(2, n) == 2 * Exp_int(2, n - 1);
  }
}

lemma DivModIdentity(y: nat, pow2n: nat, q: nat, r: nat)
  requires pow2n > 0
  requires q == y / pow2n
  requires r == y % pow2n
  ensures y == q * pow2n + r
  ensures r < pow2n
{
}

lemma ModMultAssoc(a: nat, b: nat, z: nat)
  requires z > 0
  ensures (a * b) % z == ((a % z) * (b % z)) % z
{
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
  if |sy| == 1 && sy[0] == '0' {
    var zero_str := Zeros(1);
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert 1 % Str2Int(sz) < Str2Int(sz);
    var one_str := "1";
    assert ValidBitString(one_str);
    assert Str2Int(one_str) == 1;
    var _, remainder := DivMod(one_str, sz);
    return remainder;
  }
  
  var n := |sy| - 1;
  assert n >= 0;
  
  var pow2n_str := "1" + Zeros(n);
  assert |pow2n_str| == n + 1;
  assert ValidBitString(pow2n_str);
  assert Str2Int(pow2n_str) == Exp_int(2, n);
  
  var q_str, r_str := DivMod(sy, pow2n_str);
  
  assert Str2Int(q_str) == Str2Int(sy) / Exp_int(2, n);
  assert Str2Int(r_str) == Str2Int(sy) % Exp_int(2, n);
  
  DivModIdentity(Str2Int(sy), Exp_int(2, n), Str2Int(q_str), Str2Int(r_str));
  assert Str2Int(sy) == Str2Int(q_str) * Exp_int(2, n) + Str2Int(r_str);
  
  var res1 := ModExpPow2(sx, pow2n_str, n, sz);
  assert Str2Int(res1) == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
  
  var res2: string;
  if Str2Int(q_str) == 0 {
    res2 := "1";
    assert ValidBitString(res2);
    assert Str2Int(res2) == 1;
    assert Exp_int(Str2Int(res1), 0) == 1;
  } else {
    assert |q_str| < |sy|;
    res2 := ModExp(res1, q_str, sz);
    assert Str2Int(res2) == Exp_int(Str2Int(res1), Str2Int(q_str)) % Str2Int(sz);
  }
  
  var res3: string;
  if Str2Int(r_str) == 0 {
    res3 := "1";
    assert ValidBitString(res3);
    assert Str2Int(res3) == 1;
    assert Exp_int(Str2Int(sx), 0) == 1;
  } else {
    assert |r_str| < |sy|;
    res3 := ModExp(sx, r_str, sz);
    assert Str2Int(res3) == Exp_int(Str2Int(sx), Str2Int(r_str)) % Str2Int(sz);
  }
  
  ModExpDecomposition(Str2Int(sx), Str2Int(q_str), n, Str2Int(r_str), Str2Int(sz));
  
  var prod := Add(res2, res3);
  while Str2Int(prod) >= Str2Int(sz)
    invariant ValidBitString(prod)
    invariant Str2Int(prod) % Str2Int(sz) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
    decreases Str2Int(prod)
  {
    var _, new_prod := DivMod(prod, sz);
    prod := new_prod;
  }
  
  res := prod;
}
// </vc-code>

