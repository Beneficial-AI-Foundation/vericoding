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

function BitsToInt(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * BitsToInt(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

function NatToBits(n: nat): string
  decreases n
{
  if n == 0 then "" else
    var pref := NatToBits(n / 2);
    var last := if n % 2 == 1 then "1" else "0";
    pref + last
}

lemma BitsToInt_eq_Str2Int(s: string)
  requires ValidBitString(s)
  ensures BitsToInt(s) == Str2Int(s)
  decreases s
{
  if |s| == 0 {
    // both 0
  } else {
    BitsToInt_eq_Str2Int(s[0..|s|-1]);
    // unfold definitions
    if s[|s|-1] == '1' {
      assert BitsToInt(s) == 2 * BitsToInt(s[0..|s|-1]) + 1;
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 1;
      assert BitsToInt(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
    } else {
      assert BitsToInt(s) == 2 * BitsToInt(s[0..|s|-1]) + 0;
      assert Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + 0;
      assert BitsToInt(s[0..|s|-1]) == Str2Int(s[0..|s|-1]);
    }
    // conclusion follows by above equalities
  }
}

lemma NatToBits_eq_Int2BitString(n: nat)
  ensures NatToBits(n) == Int2BitString(n)
  decreases n
{
  if n == 0 {
    // both ""
  } else {
    NatToBits_eq_Int2BitString(n / 2);
    // show last chars equal
    var pref1 := NatToBits(n / 2);
    var pref2 := Int2BitString(n / 2);
    assert pref1 == pref2;
    var last1 := if n % 2 == 1 then "1" else "0";
    var last2 := if n % 2 == 1 then "1" else "0";
    assert last1 == last2;
    assert NatToBits(n) == pref1 + last1;
    assert Int2BitString(n) == pref2 + last2;
    assert NatToBits(n) == Int2BitString(n);
  }
}

// The rest of the helper lemmas used by the algorithm.

lemma MulLeftMod(a: nat, k: nat, m: nat)
  requires m > 0
  ensures (a * k) % m == ((a % m) * k) % m
{
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
    MulLeftMod(a % m, Exp_int(a % m, n - 1), m);
    MulLeftMod(a, Exp_int(a, n - 1), m);
    // Exp_int(a % m, n) = (a % m) * Exp_int(a % m, n-1)
    // Exp_int(a, n) = a * Exp_int(a, n-1)
    // By IH and MulLeftMod these are equal modulo m
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
    // follows by multiplication
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
  var A := BitsToInt(sx);
  var E := BitsToInt(sy);
  var M := BitsToInt(sz);
  var b := A % M;
  var r := 1;
  var e := E;
  // ensure basic ranges for loop invariant at entry
  assert 0 <= b < M;
  assert 0 <= r < M;
  // Relate powers of A and A%M modulo M
  PowModBase(A, E, M);
  while e > 0
    decreases e
    invariant 0 <= r < M
    invariant 0 <= b < M
    invariant r * Exp_int(b, e) % M == Exp_int(A, E) % M
  {
    if e % 2 == 1 {
      var oldr := r;
      var olde := e;
      // update r and e for odd case
      r := (r * b) % M;
      e := e - 1;
      // prove invariant preservation for the odd step
      var t := oldr * b;
      assert t % M == r;
      assert oldr * Exp_int(b, olde) == t * Exp_int(b, olde - 1);
      MulLeftMod(t, Exp_int(b, olde - 1), M);
      assert (t * Exp_int(b, olde - 1)) % M == ((t % M) * Exp_int(b, olde - 1)) % M;
      assert ((t % M) * Exp_int(b, olde - 1)) % M == r * Exp_int(b, e) % M;
      assert r * Exp_int(b, e) % M == Exp_int(A, E) % M;
    } else {
      var oldb := b;
      var olde := e;
      // now e is even; halve e and square b
      e := e / 2;
      b := (oldb * oldb) % M;
      // relate new Exp_int(b,e) to old Exp_int(oldb,olde)
      Exp_double(oldb, e);
      PowModBase(oldb * oldb, e, M);
      assert Exp_int(b, e) % M == Exp_int(oldb, olde) % M;
      MulLeftMod(Exp_int(b, e), r, M);
      assert (Exp_int(b, e) * r) % M == ((Exp_int(b, e) % M) * r) % M;
      MulLeftMod(Exp_int(oldb, olde), r, M);
      assert (Exp_int(oldb, olde) * r) % M == ((Exp_int(oldb, olde) % M) * r) % M;
      assert ((Exp_int(b, e) % M) * r) % M == ((Exp_int(oldb, olde) % M) * r) % M;
      assert (Exp_int(b, e) * r) % M == (Exp_int(oldb, olde) * r) % M;
      // multiplication is commutative, so this gives the invariant
      assert (r * Exp_int(b, e)) % M == Exp_int(A, E) % M;
    }
  }
  // e == 0, so Exp_int(b,0) = 1 and invariant yields r % M == Exp_int(A,E) % M
  assert r * Exp_int(b, 0) % M == Exp_int(A, E) % M;
  assert r % M == Exp_int(A, E) % M;
  // since 0 <= r < M, r == r % M
  assert r == Exp_int(A, E) % M;
  // Relate the non-ghost conversions with the ghost specifications
  NatToBits_eq_Int2BitString(r);
  BitsToInt_eq_Str2Int(sx);
  BitsToInt_eq_Str2Int(sy);
  BitsToInt_eq_Str2Int(sz);
  res := NatToBits(r);
}
// </vc-code>

