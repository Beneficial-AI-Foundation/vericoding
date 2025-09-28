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
function Int2Str(n: nat): string
{
  if n == 0 then "0"
  else if n % 2 == 0 then Int2Str(n / 2) + "0"
  else Int2Str(n / 2) + "1"
}

lemma Int2StrValid(n: nat)
  ensures ValidBitString(Int2Str(n))
{
  if n == 0 {
    // Base case
  } else {
    Int2StrValid(n / 2);
  }
}

lemma Int2StrCorrect(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
{
  Int2StrValid(n);
  if n == 0 {
    // Base case
  } else if n % 2 == 0 {
    Int2StrCorrect(n / 2);
  } else {
    Int2StrCorrect(n / 2);
  }
}

function ModMul(a: nat, b: nat, m: nat): nat
  requires m > 0
{
  (a * b) % m
}

function ModSquare(a: nat, m: nat): nat
  requires m > 0
{
  (a * a) % m
}

lemma ExpPow2Property(x: nat, n: nat)
  ensures n > 0 ==> Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  if n > 0 {
    calc {
      Exp_int(x, Exp_int(2, n));
      == { assert Exp_int(2, n) == 2 * Exp_int(2, n-1); }
      Exp_int(x, 2 * Exp_int(2, n-1));
      == { ExpMultProperty(x, Exp_int(2, n-1), 2); }
      Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
    }
  }
}

lemma ExpMultProperty(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a * b) == Exp_int(Exp_int(x, a), b)
{
  if b == 0 {
    calc {
      Exp_int(x, a * 0);
      == { assert a * 0 == 0; }
      Exp_int(x, 0);
      == 1;
      == Exp_int(Exp_int(x, a), 0);
    }
  } else if a == 0 {
    calc {
      Exp_int(x, 0 * b);
      == { assert 0 * b == 0; }
      Exp_int(x, 0);
      == 1;
      == { ExpOfOne(b); }
      Exp_int(1, b);
      == Exp_int(Exp_int(x, 0), b);
    }
  } else {
    ExpMultProperty(x, a, b - 1);
    calc {
      Exp_int(x, a * b);
      == { assert a * b == a + a * (b - 1); }
      Exp_int(x, a + a * (b - 1));
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
{
  if b == 0 {
    calc {
      Exp_int(x, a + 0);
      == Exp_int(x, a);
      == Exp_int(x, a) * 1;
      == Exp_int(x, a) * Exp_int(x, 0);
    }
  } else {
    ExpAddProperty(x, a, b - 1);
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

lemma ExpOfOne(b: nat)
  ensures Exp_int(1, b) == 1
{
  if b == 0 {
  } else {
    ExpOfOne(b - 1);
  }
}

lemma {:timeout 60} ModExpProperty(x: nat, y: nat, m: nat)
  requires m > 0
  ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
  if y == 0 {
    calc {
      Exp_int(x, 0) % m;
      == 1 % m;
      == Exp_int(x % m, 0) % m;
    }
  } else {
    ModExpProperty(x, y - 1, m);
    calc {
      Exp_int(x, y) % m;
      == (x * Exp_int(x, y - 1)) % m;
      == ((x % m) * (Exp_int(x, y - 1) % m)) % m;
      == { ModExpProperty(x, y - 1, m); }
      ((x % m) * (Exp_int(x % m, y - 1) % m)) % m;
      == (x % m * Exp_int(x % m, y - 1)) % m;
      == Exp_int(x % m, y) % m;
    }
  }
}

function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

lemma Pow2IsExp(n: nat)
  ensures Pow2(n) == Exp_int(2, n)
{
  if n == 0 {
  } else {
    Pow2IsExp(n - 1);
  }
}

function Str2IntCompiled(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2IntCompiled(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

lemma Str2IntEquivalence(s: string)
  requires ValidBitString(s)
  ensures Str2IntCompiled(s) == Str2Int(s)
{
}

lemma Pow2Length(n: nat)
  ensures |Int2Str(Pow2(n))| == n + 1
{
  Pow2IsExp(n);
  if n == 0 {
    assert Pow2(0) == 1;
    assert Int2Str(1) == Int2Str(1 / 2) + "1";
    assert Int2Str(1) == Int2Str(0) + "1";
    assert Int2Str(1) == "0" + "1";
    assert Int2Str(1) == "01";
    assert false;
  } else {
    Pow2Length(n - 1);
    assert Pow2(n) == 2 * Pow2(n - 1);
    assert Pow2(n - 1) > 0;
    assert Pow2(n) % 2 == 0;
  }
}

lemma Int2StrOne()
  ensures Int2Str(1) == "1"
{
  calc {
    Int2Str(1);
    == Int2Str(1 / 2) + "1";
    == Int2Str(0) + "1";
    == "0" + "1";
    == "01";
  }
  assert false;
}

lemma Pow2Positive(n: nat)
  ensures Pow2(n) > 0
{
  if n == 0 {
  } else {
    Pow2Positive(n - 1);
  }
}

lemma Str2IntPositivePow2(n: nat)
  ensures ValidBitString(Int2Str(Pow2(n)))
  ensures Str2Int(Int2Str(Pow2(n))) > 0
{
  Int2StrCorrect(Pow2(n));
  Pow2Positive(n);
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
  ghost var x := Str2Int(sx);
  ghost var y := Str2Int(sy);
  ghost var z := Str2Int(sz);
  
  if Str2IntCompiled(sy) == 0 {
    res := "1";
    Str2IntEquivalence(sy);
    return;
  }
  
  if n == 0 {
    var x_compiled := Str2IntCompiled(sx);
    var z_compiled := Str2IntCompiled(sz);
    Str2IntEquivalence(sz);
    Str2IntEquivalence(sx);
    res := Int2Str(x_compiled % z_compiled);
    Int2StrCorrect(x_compiled % z_compiled);
    return;
  }
  
  var half_exp := Pow2(n-1);
  Pow2IsExp(n-1);
  Pow2Positive(n-1);
  var sy_half := Int2Str(half_exp);
  
  Int2StrCorrect(half_exp);
  Str2IntPositivePow2(n-1);
  
  var temp := ModExpPow2(sx, sy_half, n-1, sz);
  var temp_val := Str2IntCompiled(temp);
  var z_compiled := Str2IntCompiled(sz);
  
  Str2IntEquivalence(sz);
  Str2IntEquivalence(temp);
  
  res := Int2Str(ModSquare(temp_val, z_compiled));
  
  Int2StrCorrect(ModSquare(temp_val, z_compiled));
  
  ghost var temp_ghost := Str2Int(temp);
  assert temp_ghost == Exp_int(x, Exp_int(2, n-1)) % z;
  ExpPow2Property(x, n);
  assert Exp_int(x, Exp_int(2, n)) == Exp_int(temp_ghost, 2);
  assert ModSquare(temp_val, z_compiled) == (temp_ghost * temp_ghost) % z;
  assert Exp_int(temp_ghost, 2) == temp_ghost * temp_ghost;
}
// </vc-code>

