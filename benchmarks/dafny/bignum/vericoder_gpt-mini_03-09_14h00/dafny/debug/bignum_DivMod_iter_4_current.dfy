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

// <vc-helpers>
function pow2(k: nat): nat
  decreases k
{
  if k == 0 then 1 else 2 * pow2(k - 1)
}

lemma pow2_mul(k: nat)
  ensures pow2(k + 1) == 2 * pow2(k)
  decreases k
{
  if k == 0 {
  } else {
    pow2_mul(k - 1);
  }
}

lemma Str2IntPrepend(b: bool, s: string)
  requires ValidBitString(s)
  ensures Str2Int((if b then "1" else "0") + s) == (if b then pow2(|s|) else 0) + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // base case: Str2Int("1") == 1, Str2Int("0") == 0
  } else {
    var t := s[0..|s|-1];
    Str2IntPrepend(b, t);
    var ss := (if b then "1" else "0") + s;
    // unfold definition of Str2Int on ss
    assert |ss| > 0;
    var prefix := ss[0..|ss|-1];
    assert prefix == (if b then "1" else "0") + t;
    assert ss[|ss|-1] == s[|s|-1];
    assert Str2Int(ss) == 2 * Str2Int(prefix) + (if ss[|ss|-1] == '1' then 1 else 0);
    // Use IH on prefix
    assert Str2Int(prefix) == (if b then pow2(|t|) else 0) + Str2Int(t);
    // Combine
    assert Str2Int(ss) == 2 * ((if b then pow2(|t|) else 0) + Str2Int(t)) + (if s[|s|-1] == '1' then 1 else 0);
    // 2 * ((if b then pow2(|t|) else 0)) == (if b then 2*pow2(|t|) else 0)
    assert 2 * ((if b then pow2(|t|) else 0)) == (if b then 2 * pow2(|t|) else 0);
    // pow2(k+1) == 2*pow2(k)
    pow2_mul(|t|);
    assert (if b then 2 * pow2(|t|) else 0) == (if b then pow2(|t| + 1) else 0);
    // |t| + 1 == |s|
    assert |t| + 1 == |s|;
    assert (if b then pow2(|t| + 1) else 0) == (if b then pow2(|s|) else 0);
    // And 2*Str2Int(t) + lastbit == Str2Int(s)
    assert Str2Int(s) == 2 * Str2Int(t) + (if s[|s|-1] == '1' then 1 else 0);
    // Conclude
    assert Str2Int(ss) == (if b then pow2(|s|) else 0) + Str2Int(s);
  }
}

lemma Str2IntAppend(b: bool, t: string)
  requires ValidBitString(t)
  ensures Str2Int(t + (if b then "1" else "0")) == 2 * Str2Int(t) + (if b then 1 else 0)
  decreases |t|
{
  var s := t + (if b then "1" else "0");
  if |s| > 0 {
    var p := s[0..|s|-1];
    assert p == t;
    assert s[|s|-1] == (if b then '1' else '0');
    assert Str2Int(s) == 2 * Str2Int(p) + (if s[|s|-1] == '1' then 1 else 0);
    assert Str2Int(s) == 2 * Str2Int(t) + (if b then 1 else 0);
  }
}

lemma DivNonNeg(a: nat, b: nat)
  requires b > 0
  ensures a / b >= 0 && a % b >= 0
{
  // For naturals, division and modulus are non-negative.
}

lemma Div2Less(a: nat)
  requires a > 0
  ensures a / 2 < a
{
  if a == 1 {
    // 1/2 == 0 < 1
  } else {
    var b := a - 2;
    assert a == 2 + b;
    assert a/2 == 1 + b/2;
    // b/2 <= b holds for all nat b
    assert b/2 <= b;
    assert 1 + b/2 <= 1 + b;
    assert 1 + b == a - 1;
    assert a/2 <= a - 1;
    // Hence a/2 < a
  }
}

method ParseBitString(s: string) returns (v: nat)
  requires ValidBitString(s)
  ensures v == Str2Int(s)
{
  v := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant v == Str2Int(s[0..i])
    decreases |s| - i
  {
    var prefix := s[0..i];
    var bit := if s[i] == '1' then 1 else 0;
    // Use prepend/appending lemma to justify update
    Str2IntAppend(s[i] == '1', prefix);
    // prefix + bit-char equals s[0..i+1]
    assert prefix + (if s[i] == '1' then "1" else "0") == s[0..i+1];
    // Now update v using the arithmetic fact from lemma
    v := 2 * v + bit;
    // From Str2IntAppend and invariant v == Str2Int(prefix) before update, we get:
    assert v == Str2Int(prefix + (if s[i] == '1' then "1" else "0"));
    i := i + 1;
  }
}

method NatToBin(n: nat) returns (s: string)
  ensures ValidBitString(s)
  ensures Str2Int(s) == n
{
  s := "";
  var m := n;
  var factor := pow2(0); // 1
  // Invariant: n == m * factor + Str2Int(s)
  // and factor == pow2(|s|)
  while m != 0
    invariant ValidBitString(s)
    invariant factor == pow2(|s|)
    invariant n == m * factor + Str2Int(s)
    decreases m
  {
    var old_s := s;
    var old_m := m;
    var old_factor := factor;
    var b := m % 2;
    var ch := if b == 1 then "1" else "0";
    s := ch + s;
    m := m / 2;
    factor := factor * 2;
    // Use prepend lemma on old_s
    Str2IntPrepend(b == 1, old_s);
    // arithmetic to restore invariant
    assert old_m == 2 * m + b;
    assert old_factor == pow2(|old_s|);
    assert factor == 2 * old_factor;
    // b * old_factor == (if b == 1 then pow2(|old_s|) else 0)
    assert b * old_factor == (if b == 1 then pow2(|old_s|) else 0);
    // Combine to show n unchanged
    calc {
      n;
      == { assert n == old_m * old_factor + Str2Int(old_s); }
      old_m * old_factor + Str2Int(old_s);
      == { assert old_m == 2 * m + b; }
      (2 * m + b) * old_factor + Str2Int(old_s);
      == { assert (2 * m) * old_factor == m * (2 * old_factor); }
      m * (2 * old_factor) + b * old_factor + Str2Int(old_s);
      == { assert 2 * old_factor == factor; }
      m * factor + b * old_factor + Str2Int(old_s);
      == { assert b * old_factor == (if b == 1 then pow2(|old_s|) else 0); }
      m * factor + (if b == 1 then pow2(|old_s|) else 0) + Str2Int(old_s);
      == { assert (if b == 1 then pow2(|old_s|) else 0) + Str2Int(old_s) == Str2Int(s); }
      m * factor + Str2Int(s);
    }
    // Show decreases measure decreases: old_m > m
    Div2Less(old_m);
    assert m < old_m;
  }
  // when m == 0, invariant gives n == Str2Int(s)
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
  // Parse dividend and divisor to nat values
  var dv := ParseBitString(dividend);
  var ds := ParseBitString(divisor);
  // Ensure divisor is positive (help the verifier)
  assert ds > 0;
  // Compute quotient and remainder as integers first
  var q_int := dv / ds;
  var r_int := dv % ds;
  // They are non-negative; turn them into nat for NatToBin
  DivNonNeg(dv, ds);
  assert q_int >= 0;
  assert r_int >= 0;
  var qn: nat := q_int;
  var rn: nat := r_int;
  // Convert nats back to bit-strings
  quotient := NatToBin(qn);
  remainder := NatToBin(rn);
}
// </vc-code>

