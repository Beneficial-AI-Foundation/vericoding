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
lemma ExpPow2Lemma(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  var exp_n := Exp_int(2, n);
  var exp_n_minus_1 := Exp_int(2, n-1);
  
  assert exp_n == 2 * exp_n_minus_1;
  
  calc {
    Exp_int(x, exp_n);
    == Exp_int(x, 2 * exp_n_minus_1);
    == { ExpDoubling(x, exp_n_minus_1); }
    Exp_int(x * x, exp_n_minus_1);
    == { assert Exp_int(x, 2) == x * x; }
    Exp_int(Exp_int(x, 2), exp_n_minus_1);
    == { ExpExponent(x, 2, exp_n_minus_1); }
    Exp_int(x, 2 * exp_n_minus_1);
    == Exp_int(x, exp_n);
  }
  
  calc {
    Exp_int(x, Exp_int(2, n));
    == Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpPowerTwice(x, Exp_int(2, n-1)); }
    Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpDoubling(x: nat, n: nat)
  ensures Exp_int(x, 2*n) == Exp_int(x*x, n)
{
  if n == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x*x, 0) == 1;
  } else {
    calc {
      Exp_int(x, 2*n);
      == x * Exp_int(x, 2*n - 1);
      == x * x * Exp_int(x, 2*n - 2);
      == { if n == 1 { assert 2*n - 2 == 0; } else { ExpDoubling(x, n-1); } }
      x * x * Exp_int(x*x, n - 1);
      == Exp_int(x*x, n);
    }
  }
}

lemma ExpCommutative(x: nat, y: nat, n: nat)
  ensures Exp_int(x * y, n) == Exp_int(x, n) * Exp_int(y, n)
{
  if n == 0 {
    assert Exp_int(x * y, 0) == 1;
    assert Exp_int(x, 0) * Exp_int(y, 0) == 1 * 1 == 1;
  } else {
    calc {
      Exp_int(x * y, n);
      == (x * y) * Exp_int(x * y, n - 1);
      == { ExpCommutative(x, y, n - 1); }
      (x * y) * (Exp_int(x, n - 1) * Exp_int(y, n - 1));
      == x * Exp_int(x, n - 1) * y * Exp_int(y, n - 1);
      == Exp_int(x, n) * Exp_int(y, n);
    }
  }
}

lemma ExpExponent(x: nat, a: nat, b: nat)
  ensures Exp_int(Exp_int(x, a), b) == Exp_int(x, a * b)
{
  if b == 0 {
    assert Exp_int(Exp_int(x, a), 0) == 1;
    assert Exp_int(x, a * 0) == Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(Exp_int(x, a), b);
      == Exp_int(x, a) * Exp_int(Exp_int(x, a), b - 1);
      == { ExpExponent(x, a, b - 1); }
      Exp_int(x, a) * Exp_int(x, a * (b - 1));
      == { ExpAdd(x, a, a * (b - 1)); }
      Exp_int(x, a + a * (b - 1));
      == Exp_int(x, a * b);
    }
  }
}

lemma ExpAdd(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, a) * Exp_int(x, 0) == Exp_int(x, a) * 1 == Exp_int(x, a);
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { ExpAdd(x, a, b - 1); }
      x * Exp_int(x, a) * Exp_int(x, b - 1);
      == Exp_int(x, a) * x * Exp_int(x, b - 1);
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ExpPowerTwice(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, 2*n) == Exp_int(Exp_int(x, n), 2)
{
  calc {
    Exp_int(x, 2*n);
    == { ExpAdd(x, n, n); }
    Exp_int(x, n) * Exp_int(x, n);
    == Exp_int(Exp_int(x, n), 2);
  }
}

function CreateZeroString(n: nat): string
  ensures |CreateZeroString(n)| == n
  ensures ValidBitString(CreateZeroString(n))
  ensures Str2Int(CreateZeroString(n)) == 0
{
  if n == 0 then ""
  else "0" + CreateZeroString(n - 1)
}

function CreateOneString(): string
  ensures |CreateOneString()| == 1
  ensures ValidBitString(CreateOneString())
  ensures Str2Int(CreateOneString()) == 1
{
  "1"
}

lemma Str2IntZeroString(n: nat)
  ensures Str2Int(CreateZeroString(n)) == 0
{
  if n == 0 {
    assert CreateZeroString(0) == "";
    assert Str2Int("") == 0;
  } else {
    var s := CreateZeroString(n);
    assert s == "0" + CreateZeroString(n - 1);
    Str2IntZeroString(n - 1);
  }
}

lemma PowerOfTwoString(n: nat)
  ensures ValidBitString("1" + CreateZeroString(n))
  ensures Str2Int("1" + CreateZeroString(n)) == Exp_int(2, n)
{
  var s := "1" + CreateZeroString(n);
  assert ValidBitString(s);
  
  if n == 0 {
    assert s == "1";
    assert Str2Int("1") == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    calc {
      Str2Int(s);
      == Str2Int("1" + CreateZeroString(n));
      == { assert s[|s|-1] == '0'; assert s[0..|s|-1] == "1" + CreateZeroString(n-1); }
      2 * Str2Int("1" + CreateZeroString(n-1)) + 0;
      == { PowerOfTwoString(n-1); }
      2 * Exp_int(2, n-1);
      == Exp_int(2, n);
    }
  }
}

lemma ModuloLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{}

lemma ExpModLemma(x: nat, y: nat, m: nat)
  requires m > 1
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(x % m, 0) == 1;
  } else {
    calc {
      Exp_int(x, y) % m;
      == (x * Exp_int(x, y - 1)) % m;
      == { ModuloLemma(x, Exp_int(x, y - 1), m); }
      ((x % m) * (Exp_int(x, y - 1) % m)) % m;
      == { ExpModLemma(x, y - 1, m); }
      ((x % m) * (Exp_int(x % m, y - 1) % m)) % m;
      == { ModuloLemma(x % m, Exp_int(x % m, y - 1), m); }
      ((x % m) * Exp_int(x % m, y - 1)) % m;
      == Exp_int(x % m, y) % m;
    }
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
  if n == 0 {
    if Str2Int(sy) == 0 {
      res := CreateOneString();
      assert Exp_int(Str2Int(sx), 0) == 1;
      assert 1 < Str2Int(sz);
      assert Str2Int(res) == 1 % Str2Int(sz);
    } else {
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      
      var val := Str2Int(sx) % Str2Int(sz);
      if val == 0 {
        res := CreateZeroString(1);
      } else if val == 1 {
        res := CreateOneString();
      } else {
        res := sx;
      }
      
      ExpModLemma(Str2Int(sx), 1, Str2Int(sz));
      assert Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
    }
  } else {
    var sy_half := "1" + CreateZeroString(n - 1);
    PowerOfTwoString(n - 1);
    assert |sy_half| == n;
    assert ValidBitString(sy_half);
    assert Str2Int(sy_half) == Exp_int(2, n - 1);
    
    var temp := ModExpPow2(sx, sy_half, n - 1, sz);
    assert ValidBitString(temp);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var temp_val := Str2Int(temp);
    var squared_mod := (temp_val * temp_val) % Str2Int(sz);
    
    if squared_mod == 0 {
      res := CreateZeroString(1);
    } else if squared_mod == 1 {
      res := CreateOneString();
    } else {
      res := temp;
    }
    
    ExpPow2Lemma(Str2Int(sx), n);
    assert Exp_int(Str2Int(sx), Exp_int(2, n)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
    
    ModuloLemma(temp_val, temp_val, Str2Int(sz));
    assert Str2Int(res) == Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
  }
}
// </vc-code>

