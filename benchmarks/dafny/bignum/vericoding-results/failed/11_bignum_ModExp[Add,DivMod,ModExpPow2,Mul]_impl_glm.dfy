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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  var n := |s1|;
  var m := |s2|;
  var max_len := if n > m then n else m;
  var s1_padded := PadLeft(s1, max_len);
  var s2_padded := PadLeft(s2, max_len);
  
  var carry := 0;
  var result := "";
  var i := max_len - 1;
  
  while i >= 0
    invariant -1 <= i < max_len
    invariant 0 <= carry <= 1
    invariant ValidBitString(result)
    invariant Str2Int(result) + carry * Exp_int(2, max_len - i - 1) == 
              Str2Int(s1_padded[i+1..]) + Str2Int(s2_padded[i+1..])
  {
    var a := if s1_padded[i] == '1' then 1 else 0;
    var b := if s2_padded[i] == '1' then 1 else 0;
    var sum := a + b + carry;
    var bit := sum % 2;
    carry := sum / 2;
    result := (if bit == 1 then "1" else "0") + result;
    i := i - 1;
  }
  
  if carry == 1 {
    result := "1" + result;
  }
  
  return result;
}

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  if s1 == "0" || s2 == "0" {
    return "0";
  }
  
  var n := |s2|;
  var product := "0";
  var i := n - 1;
  
  while i >= 0
    invariant -1 <= i < n
    invariant ValidBitString(product)
    invariant Str2Int(product) == Str2Int(s1) * (Str2Int(s2[i+1..]))
  {
    if s2[i] == '1' {
      var shifted := s1 + "0" * (n - 1 - i);
      product := Add(product, shifted);
    }
    i := i - 1;
  }
  
  return product;
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  if Str2Int(dividend) < Str2Int(divisor) {
    return "0", dividend;
  }
  
  var n := |dividend|;
  var m := |divisor|;
  var current := "";
  var q := "";
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant ValidBitString(current)
    invariant ValidBitString(q)
    invariant Str2Int(current) < Str2Int(divisor)
    invariant Str2Int(q) * Str2Int(divisor) + Str2Int(current) == Str2Int(dividend[0..i])
  {
    current := current + dividend[i];
    if Str2Int(current) >= Str2Int(divisor) {
      var temp := current;
      var count := 0;
      while Str2Int(temp) >= Str2Int(divisor)
        invariant Str2Int(temp) >= 0
        invariant Str2Int(temp) + count * Str2Int(divisor) == Str2Int(current)
      {
        temp := Add(temp, divisor);
        count := count + 1;
      }
      q := q + "1";
      current := Add(current, Int2Str(count * Str2Int(divisor)));
    } else {
      q := q + "0";
    }
    i := i + 1;
  }
  
  return q, current;
}

function method PadLeft(s: string, len: int): string
  requires len >= |s|
  ensures ValidBitString(PadLeft(s, len))
  ensures |PadLeft(s, len)| == len
  ensures forall i :: |s| <= i < len ==> PadLeft(s, len)[i] == '0'
  ensures PadLeft(s, len) == "0" * (len - |s|) + s
{
  if |s| == len then s else "0" + PadLeft(s, len - 1)
}

function method Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  ensures n == 0 ==> Int2Str(n) == "0"
  ensures n > 0 ==> Int2Str(n)[0] == '1'
{
  if n == 0 then "0" else Int2StrHelper(n, "")
}

function method Int2StrHelper(n: nat, acc: string): string
  requires n > 0
  ensures ValidBitString(Int2StrHelper(n, acc))
  ensures Str2Int(Int2StrHelper(n, acc)) == n * Exp_int(2, |acc|) + Str2Int(acc)
  decreases n
{
  if n == 0 then acc else 
    Int2StrHelper(n / 2, (if n % 2 == 1 then "1" else "0") + acc)
}

function method Pow2(n: nat): nat
  ensures Pow2(n) == Exp_int(2, n)
{
  Exp_int(2, n)
}

lemma BitStringConcatProperty(s: string, t: string)
  requires ValidBitString(s) && ValidBitString(t)
  ensures Str2Int(s + t) == Str2Int(s) * Exp_int(2, |t|) + Str2Int(t)
{
  if |t| == 0 {
  } else {
    var t_first := t[0..1];
    var t_rest := t[1..];
    calc {
      Str2Int(s + t);
      Str2Int(s + t_first + t_rest);
      Str2Int(s + t_first) * Exp_int(2, |t_rest|) + Str2Int(t_rest);
      (Str2Int(s) * Exp_int(2, 1) + Str2Int(t_first)) * Exp_int(2, |t_rest|) + Str2Int(t_rest);
      Str2Int(s) * Exp_int(2, 1 + |t_rest|) + Str2Int(t_first) * Exp_int(2, |t_rest|) + Str2Int(t_rest);
      Str2Int(s) * Exp_int(2, |t|) + Str2Int(t_first + t_rest);
      Str2Int(s) * Exp_int(2, |t|) + Str2Int(t);
    }
    BitStringConcatProperty(s + t_first, t_rest);
  }
}

lemma ExpIntSplit(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
{
  if a == 0 {
    calc {
      Exp_int(x, b);
      1 * Exp_int(x, b);
      Exp_int(x, 0) * Exp_int(x, b);
    }
  } else {
    calc {
      Exp_int(x, a + b);
      Exp_int(x, (a - 1) + (b + 1));
      Exp_int(x, a - 1) * Exp_int(x, b + 1);
      Exp_int(x, a - 1) * (x * Exp_int(x, b));
      (Exp_int(x, a - 1) * x) * Exp_int(x, b);
      Exp_int(x, a) * Exp_int(x, b);
    }
    ExpIntSplit(x, a - 1, b + 1);
  }
}

lemma ModExpProperty(x: nat, y: nat, z: nat, k: nat)
  requires z > 1
  ensures Exp_int(x, y * k) % z == Exp_int(Exp_int(x, y) % z, k) % z
{
  if k == 0 {
    calc {
      Exp_int(x, y * 0) % z;
      Exp_int(x, 0) % z;
      1 % z;
      Exp_int(Exp_int(x, y) % z, 0) % z;
    }
  } else {
    calc {
      Exp_int(x, y * k) % z;
      Exp_int(x, y * (k - 1) + y) % z;
      (Exp_int(x, y * (k - 1)) * Exp_int(x, y)) % z;
      ((Exp_int(x, y * (k - 1)) % z) * (Exp_int(x, y) % z)) % z;
      ((Exp_int(Exp_int(x, y) % z, k - 1) % z) * (Exp_int(x, y) % z)) % z;
      Exp_int(Exp_int(x, y) % z, k) % z;
    }
    ExpIntSplit(x, y * (k - 1), y);
    ModExpProperty(x, y, z, k - 1);
  }
}
// </vc-helpers>
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
  var current_res := "1";
  var n := |sy|;
  var i := 0;

  ghost var y_val := Str2Int(sy);
  ghost var x_val := Str2Int(sx);
  ghost var z_val := Str2Int(sz);
  
  while i < n
    invariant 0 <= i <= n
    invariant ValidBitString(current_res)
    invariant Str2Int(current_res) == Exp_int(x_val, y_val / Pow2(n-i)) % z_val
    invariant Pow2(n-i) > 0
  {
    var square := Mul(current_res, current_res);
    var _, rem_square := DivMod(square, sz);
    current_res := rem_square;
    
    if sy[i] == '1' {
      var mul := Mul(current_res, sx);
      var _, rem_mul := DivMod(mul, sz);
      current_res := rem_mul;
    }
    
    i := i + 1;
    
    if i < n {
      BitStringConcatProperty(sy[0..i], sy[i..n]);
      calc {
        y_val / Pow2(n-i);
        Str2Int(sy) / Pow2(n-i);
        (Str2Int(sy[0..i]) * Pow2(|sy[i..n]|) + Str2Int(sy[i..n])) / Pow2(n-i);
        (Str2Int(sy[0..i]) * Pow2(n-i) + Str2Int(sy[i..n])) / Pow2(n-i);
        Str2Int(sy[0..i]) + Str2Int(sy[i..n]) / Pow2(n-i);
      }
      ModExpProperty(x_val, Pow2(i), z_val, Str2Int(sy[i..n]) / Pow2(n-i));
    }
  }
  
  res := current_res;
}
// </vc-code>

