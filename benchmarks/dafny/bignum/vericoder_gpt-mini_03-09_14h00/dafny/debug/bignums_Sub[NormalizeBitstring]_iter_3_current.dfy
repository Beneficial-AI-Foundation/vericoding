ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
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
ghost function pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

lemma Str2Int_concat(a: string, b: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures Str2Int(a + b) == Str2Int(a) * pow2(|b|) + Str2Int(b)
  decreases |b|
{
  if |b| == 0 {
    // a + "" == a and pow2(0) == 1, Str2Int("") == 0
  } else {
    var bprime := b[0..|b|-1];
    var last := b[|b|-1];
    Str2Int_concat(a, bprime);
    // Str2Int(a + b) == 2 * Str2Int(a + bprime) + lastbit
    assert Str2Int(a + b) == 2 * Str2Int(a + bprime) + (if last == '1' then 1 else 0);
    // Str2Int(b) == 2 * Str2Int(bprime) + lastbit
    assert Str2Int(b) == 2 * Str2Int(bprime) + (if last == '1' then 1 else 0);
    // pow2(|b|) == 2 * pow2(|bprime|)
    assert pow2(|b|) == 2 * pow2(|bprime|);
    // use induction hypothesis Str2Int(a + bprime) == Str2Int(a) * pow2(|bprime|) + Str2Int(bprime)
    assert 2 * Str2Int(a + bprime) + (if last == '1' then 1 else 0) ==
           2 * (Str2Int(a) * pow2(|bprime|) + Str2Int(bprime)) + (if last == '1' then 1 else 0);
    assert 2 * (Str2Int(a) * pow2(|bprime|) + Str2Int(bprime)) + (if last == '1' then 1 else 0) ==
           Str2Int(a) * (2 * pow2(|bprime|)) + (2 * Str2Int(bprime) + (if last == '1' then 1 else 0));
    assert Str2Int(a) * (2 * pow2(|bprime|)) + (2 * Str2Int(bprime) + (if last == '1' then 1 else 0)) ==
           Str2Int(a) * pow2(|b|) + Str2Int(b);
    // chain to conclude
    assert Str2Int(a + b) == Str2Int(a) * pow2(|b|) + Str2Int(b);
  }
}

method BuildBits(n: nat) returns (t: string)
  ensures ValidBitString(t)
  ensures Str2Int(t) == n
  ensures |t| > 0
  ensures |t| > 1 ==> t[0] != '0'
  decreases n
{
  if n == 0 {
    t := "0";
    return;
  }
  var q := n / 2;
  var r := n % 2;
  if q == 0 {
    // then n must be 1 and r == 1
    t := (if r == 1 then "1" else "0");
    return;
  } else {
    var prefix := BuildBits(q);
    var bit := (if r == 1 then "1" else "0");
    t := prefix + bit;
    // prove Str2Int(t) == n
    Str2Int_concat(prefix, bit);
    assert Str2Int(t) == Str2Int(prefix) * pow2(1) + Str2Int(bit);
    assert pow2(1) == 2;
    assert Str2Int(bit) == (if r == 1 then 1 else 0);
    assert Str2Int(prefix) == q;
    assert Str2Int(t) == q * 2 + r;
    assert Str2Int(t) == n;
    // ValidBitString(prefix) and single-char bit imply ValidBitString(t)
    assert ValidBitString(t);
    // prefix is normalized by induction; concatenation preserves leading-digit property
    // if q>0 then prefix[0] != '0' holds, so for |t|>1 t[0] != '0'
  }
}

function BitsToNat(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * BitsToNat(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma BitsToNat_equiv_Str2Int(s: string)
  requires ValidBitString(s)
  ensures BitsToNat(s) == Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var sprime := s[0..|s|-1];
    BitsToNat_equiv_Str2Int(sprime);
    assert BitsToNat(s) == 2 * BitsToNat(sprime) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(sprime) + (if s[|s|-1] == '1' then 1 else 0);
    assert 2 * BitsToNat(sprime) + (if s[|s|-1] == '1' then 1 else 0) ==
           2 * Str2Int(sprime) + (if s[|s|-1] == '1' then 1 else 0);
  }
}
// </vc-helpers>

// <vc-spec>
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
// </vc-spec>
// <vc-code>
{
  call BitsToNat_equiv_Str2Int(s1);
  call BitsToNat_equiv_Str2Int(s2);
  assert BitsToNat(s1) == Str2Int(s1);
  assert BitsToNat(s2) == Str2Int(s2);
  assert BitsToNat(s1) >= BitsToNat(s2);
  var d := BitsToNat(s1) - BitsToNat(s2);
  var tmp := BuildBits(d);
  res := tmp;
}
// </vc-code>

