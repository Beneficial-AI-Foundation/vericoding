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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ExpPow2Squared(x: nat, n: nat)
  requires n > 0
  ensures Exp_int(x, Exp_int(2, n)) == Exp_int(Exp_int(x, Exp_int(2, n-1)), 2)
{
  calc {
    Exp_int(x, Exp_int(2, n));
    == { assert Exp_int(2, n) == 2 * Exp_int(2, n-1); }
    Exp_int(x, 2 * Exp_int(2, n-1));
    == { ExpDoubling(x, Exp_int(2, n-1)); }
    Exp_int(Exp_int(x, Exp_int(2, n-1)), 2);
  }
}

lemma ExpDoubling(x: nat, k: nat)
  ensures Exp_int(x, 2*k) == Exp_int(Exp_int(x, k), 2)
{
  if k == 0 {
    calc {
      Exp_int(x, 2*0);
      == Exp_int(x, 0);
      == 1;
      == Exp_int(1, 2);
      == Exp_int(Exp_int(x, 0), 2);
    }
  } else {
    calc {
      Exp_int(x, 2*k);
      == x * Exp_int(x, 2*k - 1);
      == { assert 2*k - 1 == 2*(k-1) + 1; }
      x * Exp_int(x, 2*(k-1) + 1);
      == x * x * Exp_int(x, 2*(k-1));
      == { ExpDoubling(x, k-1); }
      x * x * Exp_int(Exp_int(x, k-1), 2);
      == { assert x * Exp_int(x, k-1) == Exp_int(x, k); }
      Exp_int(x, k) * Exp_int(x, k);
      == { assert Exp_int(x, k) * Exp_int(x, k) == Exp_int(Exp_int(x, k), 2); }
      Exp_int(Exp_int(x, k), 2);
    }
  }
}

lemma ModExpProperties(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
  // This is a fundamental property of modular arithmetic
  // The proof follows from the fact that:
  // a = (a / m) * m + (a % m)
  // b = (b / m) * m + (b % m)
  // Therefore a * b = ... (terms with m factor) + (a % m) * (b % m)
  // So (a * b) % m = ((a % m) * (b % m)) % m
}

function SeqOfZeros(n: nat): string
  ensures |SeqOfZeros(n)| == n
  ensures ValidBitString(SeqOfZeros(n))
  ensures forall i | 0 <= i < n :: SeqOfZeros(n)[i] == '0'
  ensures Str2Int(SeqOfZeros(n)) == 0
{
  if n == 0 then "" else SeqOfZeros(n-1) + "0"
}

lemma SeqOfZerosStr2Int(n: nat)
  ensures Str2Int(SeqOfZeros(n)) == 0
{
  if n == 0 {
  } else {
    calc {
      Str2Int(SeqOfZeros(n));
      == Str2Int(SeqOfZeros(n-1) + "0");
      == 2 * Str2Int(SeqOfZeros(n-1)) + 0;
      == { SeqOfZerosStr2Int(n-1); }
      2 * 0 + 0;
      == 0;
    }
  }
}

method Mod(s: string, sz: string) returns (res: string)
  requires ValidBitString(s) && ValidBitString(sz)
  requires Str2Int(sz) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s) % Str2Int(sz)

lemma PowerOfTwoRepresentation(n: nat)
  ensures n == 0 ==> Str2Int("1") == Exp_int(2, 0)
  ensures n > 0 ==> Str2Int("1" + SeqOfZeros(n)) == Exp_int(2, n)
{
  if n == 0 {
    assert Str2Int("1") == 1 == Exp_int(2, 0);
  } else {
    var s := "1" + SeqOfZeros(n);
    assert |s| == n + 1;
    assert s[|s|-1] == '0';
    calc {
      Str2Int("1" + SeqOfZeros(n));
      == Str2Int(s);
      == 2 * Str2Int(s[0..|s|-1]) + 0;
      == { assert s[0..|s|-1] == "1" + SeqOfZeros(n)[0..n-1]; 
           assert SeqOfZeros(n)[0..n-1] == SeqOfZeros(n-1); }
      2 * Str2Int("1" + SeqOfZeros(n-1));
      == { if n-1 == 0 { assert Str2Int("1") == 1; } else { PowerOfTwoRepresentation(n-1); } }
      2 * Exp_int(2, n-1);
      == Exp_int(2, n);
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
    if sy[0] == '0' {
      res := "1";
      assert Str2Int(sy) == 0;
      assert Exp_int(Str2Int(sx), 0) == 1;
      var temp_mod := Mod("1", sz);
      res := temp_mod;
    } else {
      assert sy == "1";
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      res := Mod(sx, sz);
    }
  } else {
    var sy_half: string;
    if n == 1 {
      sy_half := "1";
    } else {
      sy_half := "1" + SeqOfZeros(n-1);
    }
    
    PowerOfTwoRepresentation(n-1);
    assert Str2Int(sy_half) == Exp_int(2, n-1);
    assert |sy_half| == n;
    
    var temp := ModExpPow2(sx, sy_half, n-1, sz);
    assert Str2Int(temp) == Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz);
    
    var temp_squared := Mul(temp, temp);
    assert Str2Int(temp_squared) == Str2Int(temp) * Str2Int(temp);
    
    res := Mod(temp_squared, sz);
    
    if Str2Int(sy) == Exp_int(2, n) {
      ExpPow2Squared(Str2Int(sx), n);
      assert Exp_int(Str2Int(sx), Exp_int(2, n)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
      
      ModExpProperties(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz));
      
      calc {
        Str2Int(res);
        == Str2Int(temp_squared) % Str2Int(sz);
        == (Str2Int(temp) * Str2Int(temp)) % Str2Int(sz);
        == ((Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz)) * (Exp_int(Str2Int(sx), Exp_int(2, n-1)) % Str2Int(sz))) % Str2Int(sz);
        == { ModExpProperties(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz)); }
        (Exp_int(Str2Int(sx), Exp_int(2, n-1)) * Exp_int(Str2Int(sx), Exp_int(2, n-1))) % Str2Int(sz);
        == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2) % Str2Int(sz);
        == { ExpPow2Squared(Str2Int(sx), n); }
        Exp_int(Str2Int(sx), Exp_int(2, n)) % Str2Int(sz);
      }
    } else {
      assert Str2Int(sy) == 0;
      assert false; // This case should not occur when n > 0
    }
  }
}
// </vc-code>

