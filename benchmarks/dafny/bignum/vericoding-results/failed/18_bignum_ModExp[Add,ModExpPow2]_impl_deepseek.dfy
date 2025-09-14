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

// <vc-helpers>
lemma LemmaExpMod(x: nat, y: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else (x * (Exp_int(x, y - 1) % z)) % z)
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, y) % z;
      == { assert Exp_int(x, y) == x * Exp_int(x, y - 1); }
      (x * Exp_int(x, y - 1)) % z;
      == { mod_mul(x, Exp_int(x, y - 1), z); }
      (x * (Exp_int(x, y - 1) % z)) % z;
    }
  }
}

lemma LemmaExpModPow2(x: nat, n: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, Exp_int(2, n)) % z == Exp_int(x % z, Exp_int(2, n)) % z
  decreases n
{
  if n == 0 {
    assert Exp_int(2, 0) == 1;
  } else {
    LemmaExpModPow2(x, n - 1, z);
    var half_power := Exp_int(2, n - 1);
    
    calc {
      Exp_int(x, Exp_int(2, n)) % z;
      == { assert Exp_int(2, n) == 2 * half_power; }
      Exp_int(x, 2 * half_power) % z;
      == { assert Exp_int(x, 2 * half_power) == Exp_int(Exp_int(x, half_power), 2); }
      Exp_int(Exp_int(x, half_power), 2) % z;
      == { LemmaExpMod(Exp_int(x, half_power), 2, z); }
      (Exp_int(x, half_power) * (Exp_int(x, half_power) % z)) % z;
      == { LemmaExpModPow2(x, n - 1, z); }
      (Exp_int(x, half_power) * (Exp_int(x % z, half_power) % z)) % z;
      == { mod_mul(Exp_int(x, half_power), Exp_int(x % z, half_power), z); }
      (Exp_int(x, half_power) % z * (Exp_int(x % z, half_power) % z)) % z;
      == { LemmaExpModPow2(x, n - 1, z); }
      (Exp_int(x % z, half_power) % z * (Exp_int(x % z, half_power) % z)) % z;
      == { LemmaExpMod(Exp_int(x % z, half_power), 2, z); }
      Exp_int(Exp_int(x % z, half_power), 2) % z;
      == { assert Exp_int(Exp_int(x % z, half_power), 2) == Exp_int(x % z, 2 * half_power); }
      Exp_int(x % z, 2 * half_power) % z;
      == { assert 2 * half_power == Exp_int(2, n); }
      Exp_int(x % z, Exp_int(2, n)) % z;
    }
  }
}

lemma LemmaStr2IntZero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) == 0 ==> forall i | 0 <= i < |s| :: s[i] == '0'
{
  if |s| > 0 {
    var s' := s[0..|s|-1];
    assert ValidBitString(s');
    if s[|s|-1] == '1' {
      assert Str2Int(s) == 2 * Str2Int(s') + 1;
      assert Str2Int(s) != 0;
    } else {
      LemmaStr2IntZero(s');
      if Str2Int(s) == 0 {
        assert Str2Int(s') == 0;
        assert forall i | 0 <= i < |s'| :: s'[i] == '0';
        assert forall i | 0 <= i < |s| :: s[i] == '0';
      }
    }
  }
}

lemma mod_mul(x: nat, y: nat, m: nat)
  requires m > 1
  ensures (x * y) % m == (x * (y % m)) % m
{
  if y < m {
    assert y % m == y;
  } else {
    calc {
      (x * y) % m;
      == { assert y == m * (y / m) + y % m; }
      (x * (m * (y / m) + y % m)) % m;
      ==
      (x * m * (y / m) + x * (y % m)) % m;
      == 
      (x * (y % m)) % m;
    }
  }
}

lemma LemmaExp2(n: nat)
  ensures Exp_int(2, n) > 0
{
  if n > 0 {
    LemmaExp2(n-1);
  }
}

lemma LemmaPow2StrLen(n: nat, s: string)
  requires ValidBitString(s)
  requires |s| == n + 1
  ensures Str2Int(s) == Exp_int(2, n) || Str2Int(s) == 0
  decreases n
{
  if n == 0 {
    if s == "1" {
      assert Str2Int(s) == 1;
      assert Exp_int(2, 0) == 1;
    } else {
      assert s == "0";
      assert Str2Int(s) == 0;
    }
  } else {
    var s' := s[0..|s|-1];
    assert ValidBitString(s');
    assert |s'| == n;
    LemmaPow2StrLen(n-1, s');
    
    var last_char := s[|s|-1];
    if last_char == '1' {
      assert Str2Int(s) == 2 * Str2Int(s') + 1;
      if Str2Int(s') == Exp_int(2, n-1) {
        assert 2 * Exp_int(2, n-1) + 1 == Exp_int(2, n);
      } else {
        assert Str2Int(s') == 0;
        assert Str2Int(s) == 1;
        assert n == 0;
      }
    } else {
      assert Str2Int(s) == 2 * Str2Int(s');
      if Str2Int(s') == Exp_int(2, n-1) {
        assert 2 * Exp_int(2, n-1) == Exp_int(2, n);
      } else {
        assert Str2Int(s') == 0;
        assert Str2Int(s) == 0;
      }
    }
  }
}

lemma LemmaStr2IntProduct(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t)
  ensures Str2Int(s + t) == Str2Int(s) * Exp_int(2, |t|) + Str2Int(t)
  decreases |t|
{
  if |t| == 0 {
    assert s + t == s;
    assert Exp_int(2, 0) == 1;
  } else {
    var t_prefix := t[0..|t|-1];
    assert ValidBitString(t_prefix);
    LemmaStr2IntProduct(s, t_prefix);
    
    if t[|t|-1] == '1' {
      assert Str2Int(t) == 2 * Str2Int(t_prefix) + 1;
      assert Str2Int(s + t) == 2 * Str2Int(s + t_prefix) + 1;
      calc {
        Str2Int(s) * Exp_int(2, |t|) + Str2Int(t);
        == { assert Exp_int(2, |t|) == 2 * Exp_int(2, |t_prefix|); }
        Str2Int(s) * (2 * Exp_int(2, |t_prefix|)) + (2 * Str2Int(t_prefix) + 1);
        ==
        2 * (Str2Int(s) * Exp_int(2, |t_prefix|) + Str2Int(t_prefix)) + 1;
        == { LemmaStr2IntProduct(s, t_prefix); }
        2 * Str2Int(s + t_prefix) + 1;
        ==
        Str2Int(s + t);
      }
    } else {
      assert Str2Int(t) == 2 * Str2Int(t_prefix);
      assert Str2Int(s + t) == 2 * Str2Int(s + t_prefix);
      calc {
        Str2Int(s) * Exp_int(2, |t|) + Str2Int(t);
        == { assert Exp_int(2, |t|) == 2 * Exp_int(2, |t_prefix|); }
        Str2Int(s) * (2 * Exp_int(2, |t_prefix|)) + 2 * Str2Int(t_prefix);
        ==
        2 * (Str2Int(s) * Exp_int(2, |t_prefix|) + Str2Int(t_prefix));
        == { LemmaStr2IntProduct(s, t_prefix); }
        2 * Str2Int(s + t_prefix);
        ==
        Str2Int(s + t);
      }
    }
  }
}

lemma LemmaExpProduct(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    assert a + 0 == a;
    assert Exp_int(x, 0) == 1;
  } else {
    LemmaExpProduct(x, a, b-1);
    assert Exp_int(x, a + b) == x * Exp_int(x, a + b - 1);
    assert Exp_int(x, a) * Exp_int(x, b) == x * (Exp_int(x, a) * Exp_int(x, b-1));
  }
}

lemma LemmaModExpBaseCase(x: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 0) % z == 1 % z
{
  assert Exp_int(x, 0) == 1;
}

lemma LemmaModExpRecursiveCase(x: nat, y: nat, z: nat)
  requires z > 1 && y > 0
  ensures Exp_int(x, y) % z == (x * (Exp_int(x, y-1) % z)) % z
{
  LemmaExpMod(x, y, z);
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
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
      LemmaModExpBaseCase(Str2Int(sx), Str2Int(sz));
    } else {
      res := sx;
      LemmaModExpRecursiveCase(Str2Int(sx), 1, Str2Int(sz));
      mod_mul(Str2Int(sx), 1, Str2Int(sz));
    }
  } else {
    var n := |sy| - 1;
    var half_sy := sy[0..n];
    assert ValidBitString(half_sy);
    assert |half_sy| == n;
    
    var last_char := sy[n];
    var temp := ModExp(sx, half_sy, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz);
    
    if last_char == '0' {
      var square := ModExpPow2(temp, "0", n, sz);
      calc {
        Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
        == { LemmaStr2IntProduct(half_sy, "0"); }
        Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) % Str2Int(sz);
        == { LemmaExpProduct(Str2Int(sx), Str2Int(half_sy), Str2Int(half_sy)); }
        Exp_int(Exp_int(Str2Int(sx), Str2Int(half_sy)), 2) % Str2Int(sz);
        == { LemmaExpMod(Exp_int(Str2Int(sx), Str2Int(half_sy)), 2, Str2Int(sz)); }
        (Exp_int(Str2Int(sx), Str2Int(half_sy)) * (Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz))) % Str2Int(sz);
        == { assert Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz) == Str2Int(temp); }
        (Exp_int(Str2Int(sx), Str2Int(half_sy)) * Str2Int(temp)) % Str2Int(sz);
        == { mod_mul(Exp_int(Str2Int(sx), Str2Int(half_sy)), Str2Int(temp), Str2Int(sz)); }
        (Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz) * Str2Int(temp)) % Str2Int(sz);
        == { assert Exp_int(Str2Int(sx), Str2Int(half_sy)) % Str2Int(sz) == Str2Int(temp); }
        (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
        ==
        Exp_int(Str2Int(temp), 2) % Str2Int(sz);
      }
      res := square;
    } else {
      var square := ModExpPow2(temp, "0", n, sz);
      var multiplied := ModExp(sx, "1", sz);
      assert Str2Int(multiplied) == Str2Int(sx) % Str2Int(sz);
      
      var final := ModExpPow2(multiplied, "1", n, sz);
      calc {
        Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz);
        == { LemmaStr2IntProduct(half_sy, "1"); }
        Exp_int(Str2Int(sx), 2 * Str2Int(half_sy) + 1) % Str2Int(sz);
        == { LemmaExpProduct(Str2Int(sx), 2 * Str2Int(half_sy), 1); }
        (Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) * Str2Int(sx)) % Str2Int(sz);
        == { mod_mul(Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)), Str2Int(sx), Str2Int(sz)); }
        (Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) % Str2Int(sz) * Str2Int(sx)) % Str2Int(sz);
        == { assert Exp_int(Str2Int(sx), 2 * Str2Int(half_sy)) % Str2Int(sz) == Str2Int(square); }
        (Str2Int(square) * Str2Int(sx)) % Str2Int(sz);
        == { mod_mul(Str2Int(square), Str2Int(sx), Str2Int(sz)); }
        (Str2Int(square) * (
// </vc-code>

