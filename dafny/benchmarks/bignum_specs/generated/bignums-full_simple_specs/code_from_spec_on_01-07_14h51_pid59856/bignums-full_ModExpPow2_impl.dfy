//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

//ATOM

// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
    return res;
}

//ATOM

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
    quotient := "";
    remainder := "";
    assume ValidBitString(quotient) && ValidBitString(remainder);
    assume Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor);
    assume Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor);
    return quotient, remainder;
}

//ATOM

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) * Str2Int(s2);
}

//ATOM

predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

//IMPL ModExpPow2

/* code modified by LLM (iteration 1): Added helper function for power of 2 string construction */
function PowerOfTwoString(k: nat): string
{
  if k == 0 then "1" else "1" + seq(k, i => '0')
}

/* code modified by LLM (iteration 1): Added lemma for ValidBitString property of power of 2 strings */
lemma PowerOfTwoStringValid(k: nat)
  ensures ValidBitString(PowerOfTwoString(k))
{
  var s := PowerOfTwoString(k);
  if k == 0 {
    assert s == "1";
  } else {
    assert s == "1" + seq(k, i => '0');
    forall i | 0 <= i < |s|
      ensures s[i] == '0' || s[i] == '1'
    {
      if i == 0 {
        assert s[i] == '1';
      } else {
        assert s[i] == '0';
      }
    }
  }
}

/* code modified by LLM (iteration 1): Added lemma relating PowerOfTwoString to Exp_int */
lemma PowerOfTwoStringValue(k: nat)
  ensures ValidBitString(PowerOfTwoString(k))
  ensures Str2Int(PowerOfTwoString(k)) == Exp_int(2, k)
  decreases k
{
  PowerOfTwoStringValid(k);
  var s := PowerOfTwoString(k);
  
  if k == 0 {
    reveal Exp_int();
    assert s == "1";
    assert Str2Int(s) == 1;
    assert Exp_int(2, 0) == 1;
  } else {
    reveal Exp_int();
    assert s == "1" + seq(k, i => '0');
    assert |s| == k + 1;
    assert s[|s|-1] == '0';
    var prefix := s[0..|s|-1];
    assert prefix == "1" + seq(k-1, i => '0');
    assert prefix == PowerOfTwoString(k-1);
    
    PowerOfTwoStringValue(k-1);
    assert Str2Int(prefix) == Exp_int(2, k-1);
    
    calc {
      Str2Int(s);
      == 2 * Str2Int(prefix) + 0;
      == 2 * Exp_int(2, k-1);
      == Exp_int(2, k);
    }
  }
}

/* code modified by LLM (iteration 1): Added exponentiation properties lemma */
lemma ExpDoubling(base: nat, exp: nat)
  ensures Exp_int(base, 2 * exp) == Exp_int(Exp_int(base, exp), 2)
  decreases exp
{
  reveal Exp_int();
  if exp == 0 {
    calc {
      Exp_int(base, 2 * 0);
      == Exp_int(base, 0);
      == 1;
      == 1 * 1;
      == Exp_int(1, 2);
      == Exp_int(Exp_int(base, 0), 2);
    }
  } else {
    ExpDoubling(base, exp - 1);
    calc {
      Exp_int(base, 2 * exp);
      == base * Exp_int(base, 2 * exp - 1);
      == base * (base * Exp_int(base, 2 * (exp - 1)));
      == base * base * Exp_int(Exp_int(base, exp - 1), 2);
      == (base * Exp_int(base, exp - 1)) * (base * Exp_int(base, exp - 1));
      == Exp_int(base, exp) * Exp_int(base, exp);
      == Exp_int(Exp_int(base, exp), 2);
    }
  }
}

/* code modified by LLM (iteration 1): Added modular arithmetic lemma */
lemma ModularSquare(a: nat, m: nat)
  requires m > 0
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
}

// computes (sx^sy) % sz for bitstrings sx,sy,sz when str2int(sy) == 2^n
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
  /* code modified by LLM (iteration 1): Handle zero exponent case */
  if Str2Int(sy) == 0 {
    reveal Exp_int();
    res := "1";
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert 1 % Str2Int(sz) == 1;
    return;
  }
  
  /* code modified by LLM (iteration 1): Handle base case where n=0 */
  if n == 0 {
    reveal Exp_int();
    assert Str2Int(sy) == Exp_int(2, 0) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    var _, remainder := DivMod(sx, sz);
    res := remainder;
    return;
  }
  
  /* code modified by LLM (iteration 1): Handle recursive case */
  assert n > 0;
  assert Str2Int(sy) == Exp_int(2, n);
  
  // Create sy_half representing 2^(n-1)
  var sy_half := PowerOfTwoString(n-1);
  PowerOfTwoStringValue(n-1);
  
  // Recursive call
  var temp := ModExpPow2(sx, sy_half, n-1, sz);
  
  // Square the result
  var temp_squared := Mul(temp, temp);
  
  // Take modulo
  var _, remainder := DivMod(temp_squared, sz);
  res := remainder;
  
  /* code modified by LLM (iteration 1): Verify the final result using lemmas */
  reveal Exp_int();
  ExpDoubling(Str2Int(sx), Exp_int(2, n-1));
  ModularSquare(Exp_int(Str2Int(sx), Exp_int(2, n-1)), Str2Int(sz));
  
  assert Exp_int(2, n) == 2 * Exp_int(2, n-1);
  assert Exp_int(Str2Int(sx), Exp_int(2, n)) == Exp_int(Exp_int(Str2Int(sx), Exp_int(2, n-1)), 2);
}