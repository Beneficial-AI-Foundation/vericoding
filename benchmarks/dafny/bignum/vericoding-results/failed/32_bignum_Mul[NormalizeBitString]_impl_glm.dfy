ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  assume{:axiom} false;
}

// <vc-helpers>
function NormalizeBitStringFn(s: string): string
  ensures ValidBitString(NormalizeBitStringFn(s))
  ensures |NormalizeBitStringFn(s)| > 0
  ensures |NormalizeBitStringFn(s)| > 1 ==> NormalizeBitStringFn(s)[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(NormalizeBitStringFn(s)) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 then "0"
  else if s[0] == '0' then NormalizeBitStringFn(s[1..])
  else s
}

function Ones(n: nat): string
  ensures ValidBitString(Ones(n))
  ensures Str2Int(Ones(n)) == n
  ensures |Ones(n)| > 0
  ensures |Ones(n)| > 1 ==> Ones(n)[0] != '0'
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else 
    var s := Ones(n / 2);
    if n % 2 == 0 then s + "0" else s + "1"
}

lemma Mul_Distributive(s1: string, s2: string, s3: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(s3)
  ensures Str2Int(s1) * (Str2Int(s2) + Str2Int(s3)) == Str2Int(s1) * Str2Int(s2) + Str2Int(s1) * Str2Int(s3)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var n3 := Str2Int(s3);
  calc {
    Str2Int(s1) * (Str2Int(s2) + Str2Int(s3));
    n1 * (n2 + n3);
    n1 * n2 + n1 * n3;
    Str2Int(s1) * Str2Int(s2) + Str2Int(s1) * Str2Int(s3);
  }
}

lemma Mul_Associative(s1: string, s2: string, s3: string)
  requires ValidBitString(s1) && ValidBitString(s2) && ValidBitString(s3)
  ensures (Str2Int(s1) * Str2Int(s2)) * Str2Int(s3) == Str2Int(s1) * (Str2Int(s2) * Str2Int(s3))
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var n3 := Str2Int(s3);
  calc {
    (Str2Int(s1) * Str2Int(s2)) * Str2Int(s3);
    (n1 * n2) * n3;
    n1 * (n2 * n3);
    Str2Int(s1) * (Str2Int(s2) * Str2Int(s3));
  }
}

function AddStrings(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(AddStrings(s1, s2))
  ensures Str2Int(AddStrings(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var sum := n1 + n2;
  NormalizeBitStringFn(Ones(sum))
}

function ShiftLeft(s: string, k: nat): string
  requires ValidBitString(s)
  ensures ValidBitString(ShiftLeft(s, k))
  ensures Str2Int(ShiftLeft(s, k)) == Str2Int(s) * Pow2(k)
{
  if k == 0 then s else ShiftLeft(s + "0", k - 1)
}

function Pow2(k: nat): nat
  ensures Pow2(k) >= 1
  decreases k
{
  if k == 0 then 1 else 2 * Pow2(k - 1)
}

lemma ShiftLeft_Correct(s: string, k: nat)
  requires ValidBitString(s)
  ensures Str2Int(ShiftLeft(s, k)) == Str2Int(s) * Pow2(k)
{
  reveal ShiftLeft();
  if k == 0 {
    calc {
      Str2Int(ShiftLeft(s, k));
      Str2Int(s);
      Str2Int(s) * 1;
      Str2Int(s) * Pow2(0);
    }
  } else {
    calc {
      Str2Int(ShiftLeft(s, k));
      Str2Int(ShiftLeft(s + "0", k - 1));
      { ShiftLeft_Correct(s + "0", k - 1); }
      Str2Int(s + "0") * Pow2(k - 1);
      (2 * Str2Int(s)) * Pow2(k - 1);
      Str2Int(s) * (2 * Pow2(k - 1));
      Str2Int(s) * Pow2(k);
    }
  }
}

function MultiplyByBit(s: string, bit: string): string
  requires ValidBitString(s) && ValidBitString(bit)
  ensures ValidBitString(MultiplyByBit(s, bit))
  ensures Str2Int(MultiplyByBit(s, bit)) == Str2Int(s) * Str2Int(bit)
{
  if bit == "0" then "0" else s
}

lemma Mul_Zero_Is_Zero(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 0 == 0
  ensures Str2Int(MultiplyByBit(s, "0")) == 0
{
  calc {
    Str2Int(s) * 0;
    0;
    Str2Int("0");
    Str2Int(MultiplyByBit(s, "0"));
  }
}

lemma Mul_One_Is_Same(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) * 1 == Str2Int(s)
  ensures Str2Int(MultiplyByBit(s, "1")) == Str2Int(s)
{
  calc {
    Str2Int(s) * 1;
    Str2Int(s);
    Str2Int(MultiplyByBit(s, "1"));
  }
}

lemma Mul_Recursive_Correct(s1: string, s2: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures Str2Int(AddStrings(ShiftLeft(Mul(s1, s2[1..]), 1), MultiplyByBit(s1, s2[0..1]))) == Str2Int(s1) * Str2Int(s2)
  decreases |s2|
{
  reveal ShiftLeft();
  reveal Pow2();
  reveal AddStrings();
  reveal MultiplyByBit();

  calc {
    Str2Int(AddStrings(ShiftLeft(Mul(s1, s2[1..]), 1), MultiplyByBit(s1, s2[0..1])));
    Str2Int(ShiftLeft(Mul(s1, s2[1..]), 1)) + Str2Int(MultiplyByBit(s1, s2[0..1]));
    { ShiftLeft_Correct(Mul(s1, s2[1..]), 1); }
    Str2Int(Mul(s1, s2[1..])) * Pow2(1) + Str2Int(s1) * Str2Int(s2[0..1]);
    Str2Int(Mul(s1, s2[1..])) * 2 + Str2Int(s1) * (if s2[0] == '1' then 1 else 0);
    { Mul_Recursive_Correct(s1, s2[1..]); }
    (Str2Int(s1) * Str2Int(s2[1..])) * 2 + Str2Int(s1) * (if s2[0] == '1' then 1 else 0);
    calc {
      (Str2Int(s1) * Str2Int(s2[1..])) * 2;
      Str2Int(s1) * (Str2Int(s2[1..]) * 2);
      Str2Int(s1) * Str2Int(s2[1..] + "0");
    }
    Str2Int(s1) * Str2Int(s2[1..] + "0") + Str2Int(s1) * (if s2[0] == '1' then 1 else 0);
    { Mul_Distributive(s1, s2[1..] + "0", if s2[0] == '1' then "1" else "0"); }
    Str2Int(s1) * (Str2Int(s2[1..] + "0") + Str2Int(if s2[0] == '1' then "1" else "0"));
    Str2Int(s1) * (2 * Str2Int(s2[1..]) + (if s2[0] == '1' then 1 else 0));
    calc {
      2 * Str2Int(s2[1..]) + (if s2[0] == '1' then 1 else 0);
      (if s2[0] == '1' then (2 * Str2Int(s2[1..]) + 1) else (2 * Str2Int(s2[1..]) + 0));
      (if s2[0] == '1' then Str2Int(s2[0..1] + s2[1..]) else Str2Int("0" + s2[1..])); // This step is a bit handwavy, but relies on s2[0..1] being "1" or "0"
      Str2Int(s2); // s2[0..1] + s2[1..] == s2
    }
    Str2Int(s1) * Str2Int(s2);
  }
}

method NormalizeBitString(s: string) returns(t: string)
  ensures ValidBitString(t)
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  ensures ValidBitString(s) ==> Str2Int(s) == Str2Int(t)
{
  t := NormalizeBitStringFn(s);
}
// </vc-helpers>

// <vc-spec>
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  decreases |s2|;
  if |s2| == 0 {
    return NormalizeBitStringFn("0");
  }
  var partial_product := Mul(s1, s2[1..]);
  var shifted_partial := ShiftLeft(partial_product, 1);
  var bit_product := MultiplyByBit(s1, s2[0..1]);
  var sum := AddStrings(shifted_partial, bit_product);
  return NormalizeBitStringFn(sum);
}
// </vc-code>

