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

// <vc-helpers>
lemma ExpPow2Property(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpMultProperty(x, Exp_int(2, n-1), 2); }
    Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
  decreases b
{
  if b == 0 {
    assert a * b == 0;
    assert Exp_int(x, 0) == 1;
    assert Exp_int(Exp_int(x, a), 0) == 1;
  } else {
    calc {
      Exp_int(x, a * b);
      == Exp_int(x, a + a * (b - 1));
      == { ExpAddProperty(x, a, a * (b - 1)); }
      Exp_int(x, a) * Exp_int(x, a * (b - 1));
      == { ExpMultProperty(x, a, b - 1); }
      Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == Exp_int(Exp_int(x, a), b);
    }
  }
}

lemma ExpAddProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, a + b) == Exp_int(x, a);
    assert Exp_int(x, a) * 1 == Exp_int(x, a);
  } else {
    calc {
      Exp_int(x, a + b);
      == Exp_int(x, a + (b - 1) + 1);
      == x * Exp_int(x, a + (b - 1));
      == { ExpAddProperty(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModSquareProperty(a: nat, m: nat)
  requires m > 1
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
  calc {
    (a * a) % m;
    == ((a % m + (a / m) * m) * (a % m + (a / m) * m)) % m;
    == ((a % m) * (a % m) + (a % m) * ((a / m) * m) + ((a / m) * m) * (a % m) + ((a / m) * m) * ((a / m) * m)) % m;
    == ((a % m) * (a % m)) % m;
  }
}

function ExpIntCompute(x: nat, y: nat): nat
{
  if y == 0 then 1 else x * ExpIntCompute(x, y - 1)
}

lemma ExpIntComputeCorrect(x: nat, y: nat)
  ensures ExpIntCompute(x, y) == Exp_int(x, y)
{
}

function Str2IntCompute(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else (2 * Str2IntCompute(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntComputeCorrect(s: string)
  requires ValidBitString(s)
  ensures Str2IntCompute(s) == Str2Int(s)
{
}

method Int2Str(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
  ensures Str2IntCompute(s) == n
{
  if n == 0 {
    s := "0";
  } else {
    var q := n / 2;
    var r := n % 2;
    var qs := Int2Str(q);
    var bit := if r == 1 then "1" else "0";
    s := qs + bit;
    
    assert Str2Int(s) == 2 * Str2Int(qs) + r;
    assert Str2Int(qs) == q;
    assert n == 2 * q + r;
    Str2IntComputeCorrect(s);
  }
}

predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma ZeroStringMeansZero(s: string)
  requires ValidBitString(s)
  requires IsZeroString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
    assert Str2Int(s) == 0;
  } else {
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert IsZeroString(prefix);
    ZeroStringMeansZero(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) + 0 == 0;
  }
}

lemma NonZeroStringMeansNonZero(s: string)
  requires ValidBitString(s)
  requires !IsZeroString(s)
  ensures Str2Int(s) > 0
{
  if |s| == 0 {
    assert IsZeroString(s);
    assert false;
  } else if s[|s|-1] == '1' {
    assert Str2Int(s) >= 1;
  } else {
    var prefix := s[0..|s|-1];
    assert !IsZeroString(prefix);
    NonZeroStringMeansNonZero(prefix);
    assert Str2Int(s) == 2 * Str2Int(prefix) > 0;
  }
}

method IsZero(s: string) returns (isZero: bool)
  requires ValidBitString(s)
  ensures isZero <==> IsZeroString(s)
  ensures isZero <==> Str2Int(s) == 0
{
  isZero := true;
  for i := 0 to |s|
    invariant isZero <==> forall j | 0 <= j < i :: s[j] == '0'
  {
    if s[i] != '0' {
      isZero := false;
    }
  }
  
  if isZero {
    ZeroStringMeansZero(s);
  } else {
    NonZeroStringMeansNonZero(s);
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
  var isYZero := IsZero(sy);
  
  if isYZero {
    // x^0 = 1
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sz);
    var one := Int2Str(1 % z_val);
    res := one;
  } else if n == 0 {
    // sy = 2^0 = 1, so x^1 = x
    var x_val := Str2IntCompute(sx);
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sx);
    Str2IntComputeCorrect(sz);
    var result := Int2Str(x_val % z_val);
    res := result;
  } else {
    // sy = 2^n where n > 0
    // Compute x^(2^(n-1)) mod z recursively
    var half_exp := ExpIntCompute(2, n-1);
    ExpIntComputeCorrect(2, n-1);
    var half_exp_str := Int2Str(half_exp);
    assert Str2Int(half_exp_str) == Exp_int(2, n-1);
    
    var temp := ModExpPow2(sx, half_exp_str, n-1, sz);
    
    // Now square the result: (x^(2^(n-1)))^2 mod z
    var temp_val := Str2IntCompute(temp);
    Str2IntComputeCorrect(temp);
    assert temp_val == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var z_val := Str2IntCompute(sz);
    Str2IntComputeCorrect(sz);
    var squared_val := (temp_val * temp_val) % z_val;
    
    ExpPow2Property(Str2Int(sx), n);
    assert Exp_int(Str2Int(sx), Exp_int(2, n)) == 
           Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
    
    ModSquareProperty(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz));
    
    var result := Int2Str(squared_val);
    res := result;
  }
}
// </vc-code>

