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

// <vc-helpers>
ghost function Int2BitString(n: nat): string
  ensures ValidBitString(Int2BitString(n))
  ensures Str2Int(Int2BitString(n)) == n
  decreases n
{
  if n == 0 then "" else
    var pref := Int2BitString(n / 2);
    var last := if n % 2 == 1 then "1" else "0";
    pref + last
}

lemma MulLeftMod(a: nat, k: nat, m: nat)
  requires m > 0
  ensures (a * k) % m == ((a % m) * k) % m
{
  // a = (a % m) + m * (a / m)
  var t := a / m;
  assert a == a % m + m * t;
  assert a * k == (a % m) * k + m * (t * k);
  // therefore both have same remainder modulo m
}

lemma PowModBase(a: nat, n: nat, m: nat)
  requires m > 0
  ensures Exp_int(a % m, n) % m == Exp_int(a, n) % m
  decreases n
{
  if n == 0 {
    // both sides are 1 % m
  } else {
    PowModBase(a, n - 1, m);
    // Exp_int(a % m, n) = (a % m) * Exp_int(a % m, n-1)
    // By IH Exp_int(a % m, n-1) % m == Exp_int(a, n-1) % m
    // Use MulLeftMod to relate (a % m) * Exp_int(a, n-1) and a * Exp_int(a, n-1)
    MulLeftMod(a, Exp_int(a, n - 1), m);
    // conclude ((a % m) * Exp_int(a, n-1)) % m == (a * Exp_int(a, n-1)) % m == Exp_int(a,n) % m
  }
}

lemma Exp_double(b: nat, q: nat)
  ensures Exp_int(b * b, q) == Exp_int(b, 2 * q)
  decreases q
{
  if q == 0 {
    // both 1
  } else {
    Exp_double(b, q - 1);
    // Exp_int(b*b, q) = (b*b) * Exp_int(b*b, q-1)
    // By IH Exp_int(b*b, q-1) == Exp_int(b, 2*(q-1))
    // So left = b*b * Exp_int(b, 2*(q-1)) = Exp_int(b, 2*q)
  }
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
  var A := Str2Int(sx);
  var E := Str2Int(sy);
  var M := Str2Int(sz);
  var b := A % M;
  var r := 1;
  var e := E;
  // Use lemma to relate Exp_int(A%M, E) % M and Exp_int(A, E) % M
  PowModBase(A, E, M);
  // Invariant: r * Exp_int(b, e) % M == Exp_int(A, E) % M
  while e > 0
    decreases e
    invariant 0 <= r < M
    invariant 0 <= b < M
    invariant r * Exp_int(b, e) % M == Exp_int(A, E) % M
  {
    if e % 2 == 1 {
      var ro := r;
      var bo := b;
      var eo := e;
      // update r and e for odd case
      r := (r * b) % M;
      e := e - 1;
      // prove invariant preservation for the odd step
      var t := ro * bo;
      assert t % M == r;
      // ro * Exp_int(bo, eo) == t * Exp_int(bo, eo - 1)
      assert ro * Exp_int(bo, eo) == t * Exp_int(bo, eo - 1);
      MulLeftMod(t, Exp_int(bo, eo - 1), M);
      assert (t * Exp_int(bo, eo - 1)) % M == ((t % M) * Exp_int(bo, eo - 1)) % M;
      assert ((t % M) * Exp_int(bo, eo - 1)) % M == r * Exp_int(b, e) % M;
      assert r * Exp_int(b, e) % M == ro * Exp_int(bo, eo) % M;
      // combined with previous invariant (ro * Exp_int(bo, eo) % M == Exp_int(A,E) % M) preserves invariant
    }
    // Now e is even; perform halving and squaring
    var bo2 := b;
    var eo2 := e;
    assert eo2 % 2 == 0;
    assert eo2 == 2 * (eo2 / 2);
    e := e / 2;
    b := (bo2 * bo2) % M;
    // prove invariant preservation for the even (halving) step
    Exp_double(bo2, eo2 / 2);
    PowModBase(bo2 * bo2, eo2 / 2, M);
    // From PowModBase and Exp_double we get Exp_int(b, e) % M == Exp_int(bo2, eo2) % M
    assert Exp_int(b, e) % M == Exp_int(bo2, eo2) % M;
    // use MulLeftMod to lift equality under multiplication by r
    MulLeftMod(Exp_int(b, e), r, M);
    assert (Exp_int(b, e) * r) % M == ((Exp_int(b, e) % M) * r) % M;
    assert ((Exp_int(b, e) % M) * r) % M == ((Exp_int(bo2, eo2) % M) * r) % M;
    assert ((Exp_int(bo2, eo2) % M) * r)
// </vc-code>

