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

// <vc-helpers>
lemma Exp_int_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if b == 0 {
    assert Exp_int(x, a + 0) == Exp_int(x, a);
    assert Exp_int(x, 0) == 1;
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, a + b - 1);
      == { Exp_int_add(x, a, b - 1); }
      x * Exp_int(x, a) * Exp_int(x, b - 1);
      == Exp_int(x, a) * (x * Exp_int(x, b - 1));
      == Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

lemma ModExpDecomposition(x: nat, y: nat, z: nat, highBit: nat, lowBits: nat)
  requires z > 1
  requires y == Exp_int(2, highBit) + lowBits
  requires lowBits < Exp_int(2, highBit)
  ensures Exp_int(x, y) % z == (Exp_int(x, Exp_int(2, highBit)) % z * Exp_int(x, lowBits) % z) % z
{
  Exp_int_add(x, Exp_int(2, highBit), lowBits);
  assert Exp_int(x, y) == Exp_int(x, Exp_int(2, highBit)) * Exp_int(x, lowBits);
}

function StringWithHighBitSet(n: nat): string
  requires n >= 0
  ensures ValidBitString(StringWithHighBitSet(n))
  ensures |StringWithHighBitSet(n)| == n + 1
  ensures Str2Int(StringWithHighBitSet(n)) == Exp_int(2, n)
{
  if n == 0 then "1"
  else "0" + StringWithHighBitSet(n - 1)
}

lemma StringWithHighBitSetCorrect(n: nat)
  requires n >= 0
  ensures Str2Int(StringWithHighBitSet(n)) == Exp_int(2, n)
{
  if n == 0 {
  } else {
    calc {
      Str2Int(StringWithHighBitSet(n));
      == Str2Int("0" + StringWithHighBitSet(n - 1));
      == 2 * Str2Int(StringWithHighBitSet(n - 1)) + 0;
      == { StringWithHighBitSetCorrect(n - 1); }
      2 * Exp_int(2, n - 1);
      == Exp_int(2, n);
    }
  }
}

predicate IsZeroString(s: string)
  requires ValidBitString(s)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

lemma IsZeroStringImpliesZero(s: string)
  requires ValidBitString(s)
  requires IsZeroString(s)
  ensures Str2Int(s) == 0
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    IsZeroStringImpliesZero(s[0..|s|-1]);
  }
}

lemma ZeroImpliesIsZeroString(s: string)
  requires ValidBitString(s)
  requires Str2Int(s) == 0
  ensures IsZeroString(s)
{
  if |s| == 0 {
  } else {
    if s[|s|-1] == '1' {
      assert Str2Int(s) >= 1;
      assert false;
    }
    assert s[|s|-1] == '0';
    ZeroImpliesIsZeroString(s[0..|s|-1]);
  }
}

function IsAllZeros(s: string): bool
  requires ValidBitString(s)
  ensures IsAllZeros(s) <==> IsZeroString(s)
{
  if |s| == 0 then true
  else if s[|s|-1] == '1' then false
  else IsAllZeros(s[0..|s|-1])
}

lemma ModExpSimple(x: nat, y: nat, z: nat)
  requires z > 1
  requires y == 0
  ensures Exp_int(x, y) % z == 1 % z
{
  assert Exp_int(x, 0) == 1;
}

lemma ModExpOne(x: nat, z: nat)
  requires z > 1
  ensures Exp_int(x, 1) % z == x % z
{
  assert Exp_int(x, 1) == x;
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
    // y == 0, return 1
    res := "1";
    assert Str2Int(sy) == 0;
    assert Exp_int(Str2Int(sx), 0) == 1;
    assert Str2Int(res) == 1;
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    // y == 1, return x % z
    var q, r := DivMod(sx, sz);
    res := r;
    assert Str2Int(sy) == 1;
    assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
    assert Str2Int(res) == Str2Int(sx) % Str2Int(sz);
    return;
  }

  // For y > 1, use decomposition y = 2^(|sy|-1) + remainder
  var n := |sy| - 1;
  var highBitStr := StringWithHighBitSet(n);
  
  // Calculate x^(2^n) % z
  var partialRes := ModExpPow2(sx, highBitStr, n, sz);
  
  // Calculate remainder of y / 2^n
  var q, r := DivMod(sy, highBitStr);
  
  if IsAllZeros(r) {
    // y is exactly 2^n
    res := partialRes;
    IsZeroStringImpliesZero(r);
    assert Str2Int(r) == 0;
    assert Str2Int(sy) == Str2Int(highBitStr);
    assert Str2Int(sy) == Exp_int(2, n);
  } else {
    // y = 2^n + remainder, use recursive call
    var recursiveRes := ModExp(sx, r, sz);
    
    // Multiply partialRes and recursiveRes modulo sz
    // This is (x^(2^n) % z) * (x^r % z) % z
    var temp := "0";
    var i := 0;
    ghost var recursiveInt := Str2Int(recursiveRes);
    
    while i < recursiveInt
      invariant 0 <= i <= recursiveInt
      invariant ValidBitString(temp)
      invariant Str2Int(temp) == (Str2Int(partialRes) * i) % Str2Int(sz)
    {
      temp := Add(temp, partialRes);
      var qTemp, rTemp := DivMod(temp, sz);
      temp := rTemp;
      i := i + 1;
    }
    
    res := temp;
    
    // Correctness follows from ModExpDecomposition
    assert Str2Int(sy) == Str2Int(q) * Str2Int(highBitStr) + Str2Int(r);
    assert Str2Int(highBitStr) == Exp_int(2, n);
    assert Str2Int(r) < Exp_int(2, n);
    ModExpDecomposition(Str2Int(sx), Str2Int(sy), Str2Int(sz), n, Str2Int(r));
  }
}
// </vc-code>

