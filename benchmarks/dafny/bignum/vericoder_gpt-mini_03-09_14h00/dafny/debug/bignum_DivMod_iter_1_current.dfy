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

lemma Str2IntPrepend(b: bool, s: string)
  requires ValidBitString(s)
  ensures Str2Int((if b then "1" else "0") + s) == (if b then pow2(|s|) else 0) + Str2Int(s)
  decreases |s|
{
  if |s| == 0 {
    // Str2Int((if b then "1" else "0")) == (if b then 1 else 0) == (if b then pow2(0) else 0) + 0
  } else {
    var t := s[0..|s|-1];
    Str2IntPrepend(b, t);
    // By definition of Str2Int:
    // Str2Int((if b then "1" else "0") + s) = 2*Str2Int((if b then "1" else "0") + t) + (if s[|s|-1]=='1' then 1 else 0)
    // By IH, Str2Int((if b then "1" else "0") + t) = (if b then pow2(|t|) else 0) + Str2Int(t)
    // Hence result = (if b then 2*pow2(|t|) else 0) + 2*Str2Int(t) + (if s[|s|-1]=='1' then 1 else 0)
    // 2*pow2(|t|) = pow2(|t|+1) = pow2(|s|)
    // and 2*Str2Int(t) + lastbit = Str2Int(s)
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
  {
    v := 2 * v + (if s[i] == '1' then 1 else 0);
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
  {
    var b := m % 2;
    var ch := if b == 1 then "1" else "0";
    // Prepend ch to s
    s := ch + s;
    m := m / 2;
    factor := factor * 2;
    // Need to justify the invariant update:
    // Str2Int(ch + old_s) == (if b==1 then pow2(|old_s|) else 0) + Str2Int(old_s)
    // which is exactly Str2IntPrepend(b==1, old_s)
    Str2IntPrepend(b == 1, s[1..|s|]); // s[1..|s|] is old_s after prepend
    // Note: the arithmetic reasoning for n == m*factor + Str2Int(s) follows from the update.
  }
  // When m == 0, n == Str2Int(s)
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
  // Compute quotient and remainder as nats
  var qn := dv / ds;
  var rn := dv % ds;
  // Convert nats back to bit-strings
  quotient := NatToBin(qn);
  remainder := NatToBin(rn);
}
// </vc-code>

