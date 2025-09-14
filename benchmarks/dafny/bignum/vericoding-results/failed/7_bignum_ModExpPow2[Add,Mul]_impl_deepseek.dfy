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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpIntZero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma ExpIntMul(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ExpIntPowerOfTwo(n: nat)
  ensures Exp_int(2, n) == (pow2(n) as nat)
  decreases n
{
  if n > 0 {
    ExpIntPowerOfTwo(n - 1);
    assert Exp_int(2, n) == 2 * Exp_int(2, n - 1);
  }
}

function pow2(n: nat): int
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma ModExpPowerOfTwoHelper(x: nat, y: nat, z: nat)
  requires z > 1
  requires y == 0 || exists n :: y == (pow2(n) as nat)
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else (Exp_int(x, y/2) % z) * (Exp_int(x, y/2) % z) % z)
  decreases y
{
  if y == 0 {
    // Base case: x^0 mod z = 1 mod z
  } else {
    // y is a power of 2, so y/2 = y >> 1 is also a power of 2 or 0
    var half := y/2;
    assert y == 2 * half;
    assert Exp_int(x, y) == Exp_int(x, half) * Exp_int(x, half);
    assert Exp_int(x, y) % z == (Exp_int(x, half) % z) * (Exp_int(x, half) % z) % z;
  }
}

lemma ModuloMultiplication(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

ghost function IsPowerOfTwo(y: nat): bool
{
  y == 0 || exists n :: y == (pow2(n) as nat)
}

ghost function NatToBitString(n: nat): string
  ensures ValidBitString(result)
  ensures Str2Int(result) == n
  decreases n
{
  if n == 0 then
    "0"
  else if n % 2 == 0 then
    NatToBitString(n / 2) + "0"
  else
    NatToBitString(n / 2) + "1"
}

lemma HalfStringProperties(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  ensures ValidBitString("0" + sy[1..])
  ensures |"0" + sy[1..]| == n
  ensures Str2Int("0" + sy[1..]) == (if Str2Int(sy) == 0 then 0 else Exp_int(2, n - 1))
{
}

lemma HalfStringValue(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  ensures Str2Int("0" + sy[1..]) == Str2Int(sy) / 2
{
}

lemma ExpIntDivision(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == Exp_int(x, y/2) * Exp_int(x, y/2)
{
}

lemma ExpIntPowerOfTwoHalving(n: nat)
  requires n > 0
  ensures Exp_int(2, n) == 2 * Exp_int(2, n-1)
{
}

lemma Str2IntDivision(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  ensures Str2Int("0" + sy[1..]) == Str2Int(sy) / 2
{
}

lemma PowerOfTwoHalf(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  ensures Str2Int("0" + sy[1..]) == Exp_int(2, n - 1) || Str2Int("0" + sy[1..]) == 0
{
}

lemma RecursiveCallPrecondition(half_sy: string, half_n: nat, sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
  requires half_sy == "0" + sy[1..]
  requires half_n == n - 1
  requires n > 0
  ensures ValidBitString(half_sy) && |half_sy| == half_n + 1
  ensures Str2Int(half_sy) == Exp_int(2, half_n) || Str2Int(half_sy) == 0
{
}

lemma RecursiveCallCorrectness(sx: string, half_sy: string, half_n: nat, sz: string)
  requires ValidBitString(sx) && ValidBitString(half_sy) && ValidBitString(sz)
  requires |half_sy| == half_n + 1
  requires Str2Int(half_sy) == Exp_int(2, half_n) || Str2Int(half_sy) == 0
  requires Str2Int(sz) > 1
  ensures ValidBitString(ModExpPow2(sx, half_sy, half_n, sz))
  ensures Str2Int(ModExpPow2(sx, half_sy, half_n, sz)) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz)
{
}

lemma ExpIntHalfPower(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(x, Exp_int(2, n-1)) * Exp_int(x, Exp_int(2, n-1))
{
  var half := Exp_int(2, n-1);
  assert Exp_int(2, n) == 2 * half;
  assert Exp_int(x, Exp_int(2, n)) == Exp_int(x, half * 2);
  assert Exp_int(x, half * 2) == Exp_int(x, half) * Exp_int(x, half);
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
  var x_val := Str2Int(sx);
  var y_val := Str2Int(sy);
  var z_val := Str2Int(sz);
  
  if n == 0 {
    if y_val == 0 {
      var res_val := 1 % z_val;
      res := NatToBitString(res_val);
    } else {
      assert y_val == 1;
      var res_val := x_val % z_val;
      res := NatToBitString(res_val);
    }
  } else {
    var half_n := n - 1;
    var half_sy := "0" + sy[1..];
    HalfStringProperties(sy, n);
    RecursiveCallPrecondition(half_sy, half_n, sy, n);
    
    var half_res := ModExpPow2(sx, half_sy, half_n, sz);
    RecursiveCallCorrectness(sx, half_sy, half_n, sz);
    assert Str2Int(half_res) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz);
    
    var squared := Mul(half_res, half_res);
    var squared_val := Str2Int(squared);
    
    var mod_val := squared_val % z_val;
    res := NatToBitString(mod_val);
    
    assert Exp_int(Str2Int(sx), Str2Int(sy)) == Exp_int(x_val, y_val);
    assert y_val == Exp_int(2, n);
    ExpIntHalfPower(x_val, n);
    assert Exp_int(x_val, y_val) == Exp_int(x_val, Exp_int(2, n-1)) * Exp_int(x_val, Exp_int(2, n-1));
    assert Str2Int(half_sy) == Exp_int(2, n-1) || Str2Int(half_sy) == 0;
    if Str2Int(half_sy) == 0 {
      assert y_val == 0;
    } else {
      assert Str2Int(half_sy) == Exp_int(2, n-1);
      assert Exp_int(Str2Int(sx), Str2Int(half_sy)) == Exp_int(x_val, Exp_int(2, n-1));
    }
    ModuloMultiplication(Str2Int(half_res), Str2Int(half_res), z_val);
  }
}
// </vc-code>

