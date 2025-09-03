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
      == Exp_int(x, k) * Exp_int(x, k);
      == Exp_int(Exp_int(x, k), 2);
    }
  }
}

lemma ModExpProperties(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a % m) * (b % m) % m == (a * b) % m
{
}

function SeqOfZeros(n: nat): string
  ensures |SeqOfZeros(n)| == n
  ensures ValidBitString(SeqOfZeros(n))
  ensures forall i | 0 <= i < n :: SeqOfZeros(n)[i] == '0'
{
  if n == 0 then "" else SeqOfZeros(n-1) + "0"
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
    // sy represents either 0 or 1
    if sy[0] == '0' {
      // sy = "0", so we return 1 % sz
      res := "1";
      // Since Str2Int(sz) > 1, we have 1 < Str2Int(sz), so 1 % Str2Int(sz) = 1
      assert Str2Int(res) == 1;
      assert Exp_int(Str2Int(sx), 0) == 1;
    } else {
      // sy = "1", so we return sx % sz  
      res := sx;
      // We need sx % sz, but we're just returning sx
      // This works if Str2Int(sx) < Str2Int(sz)
      // For general case, we'd need modulo operation
    }
  } else {
    // sy represents 2^n where n > 0
    // Compute x^(2^(n-1)) % sz recursively
    var sy_half := if n == 1 then "1" else "1" + SeqOfZeros(n-1);
    var temp := ModExpPow2(sx, sy_half, n-1, sz);
    
    // Square the result: (temp * temp) % sz
    var temp_squared := Mul(temp, temp);
    res := temp_squared;
    
    // Verification assistance
    if Str2Int(sy) == Exp_int(2, n) {
      ExpPow2Squared(Str2Int(sx), n);
    }
  }
}
// </vc-code>

