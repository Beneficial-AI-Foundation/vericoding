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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
function Int2Str(n: nat): string
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then "" else Int2Str(n / 2) + (if n % 2 == 1 then "1" else "0")
}

function ParseBits(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then 0 else 2 * ParseBits(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
}

lemma ParseBitsEqualsStr2Int(s: string)
  requires ValidBitString(s)
  ensures ParseBits(s) == Str2Int(s)
  decreases s
{
  if |s| > 0 {
    ParseBitsEqualsStr2Int(s[0..|s|-1]);
  }
}

lemma Exp_succ(x: nat, y: nat)
  ensures Exp_int(x, y + 1) == x * Exp_int(x, y)
  decreases y
{
  if y > 0 {
    Exp_succ(x, y - 1);
  }
}

lemma Exp_add(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b > 0 {
    Exp_add(x, a, b - 1);
  }
}

lemma Exp_double(vx: nat, i: nat)
  ensures Exp_int(2, i + 1) == Exp_int(2, i) + Exp_int(2, i)
  ensures Exp_int(vx, Exp_int(2, i + 1)) == Exp_int(vx, Exp_int(2, i)) * Exp_int(vx, Exp_int(2, i))
  decreases i
{
  // Exp_int(2, i+1) == 2 * Exp_int(2, i)
  Exp_succ(2, i);
  var t := Exp_int(2, i);
  assert Exp_int(2, i + 1) == 2 * t;
  // 2*t == t + t
  assert 2 * t == t + t;
  // therefore Exp_int(vx, Exp_int(2,i+1)) == Exp_int(vx, t+t)
  Exp_add(vx, t, t);
  assert Exp_int(vx, t + t) == Exp_int(vx, t) * Exp_int(vx, t);
  assert Exp_int(vx, Exp_int(2, i + 1)) == Exp_int(vx, t + t);
  assert Exp_int(vx, Exp_int(2, i + 1)) == Exp_int(vx, Exp_int(2, i)) * Exp_int(vx, Exp_int(2, i));
}

lemma DivModUnique(z: nat, m: nat, q: nat, r: nat)
  requires m > 0
  requires r < m
  requires z == m * q + r
  ensures z / m == q && z % m == r
{
  var q' := z / m;
  var r' := z % m;
  // z decomposes both as m*q + r and m*q' + r'
  assert z == m * q + r;
  assert z == m * q' + r';
  // switch to ints for easier algebra
  var iz := z as int;
  var im := m as int;
  var iq := q as int;
  var ir := r as int;
  var iq' := q' as int;
  var ir' := r' as int;
  assert iz == im * iq + ir;
  assert iz == im * iq' + ir';
  // rearrange difference: im*(iq - iq') + (ir - ir') == 0
  assert im * (iq - iq') + (ir - ir') == 0;
  assert (ir - ir') == im * (iq' - iq);
  // bounds for remainders
  assert 0 <= ir < im;
  assert 0 <= ir' < im;
  // hence |ir - ir'| < im, but ir - ir' is a multiple of im, so it must be zero
  if iq' - iq != 0 {
    if iq' - iq > 0 {
      // im * (iq' - iq) >= im, contradicts < im
      assert im <= im * (iq' - iq);
      assert im * (iq' - iq) == ir - ir';
      assert ir - ir' < im;
      reveal im <= ir - ir'; // this will produce contradiction
    } else {
      // iq' - iq < 0
      assert im <= im * (iq - iq');
      assert im * (iq - iq') == ir' - ir;
      assert ir' - ir < im;
      reveal im <= ir' - ir; // contradiction
    }
  }
  // From contradictions above we conclude iq' - iq == 0
  assert iq' - iq == 0;
  assert ir - ir' == 0;
  assert ir == ir';
  assert iq == iq';
  // conclude the division/modulus equalities
  assert z / m == q';
  assert q' == q;
  assert z % m == r';
  assert r' == r;
}

lemma ModAddMulRight(x: nat, y: nat, m: nat)
  requires m > 0
  ensures (x + m * y) % m == x % m
{
  var qx := x / m;
  var rx := x % m;
  assert x == m * qx + rx;
  var z := x + m * y;
  assert z == m * (qx + y) + rx;
  DivModUnique(z, m, qx + y, rx);
  assert z % m == rx;
  assert rx == x % m;
}

lemma ModMulCompatibility(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var qa := a / m;
  var ra := a % m;
  var qb := b / m;
  var rb := b % m;
  assert 0 <= ra < m;
  assert 0 <= rb < m;
  assert a == m * qa + ra;
  assert b == m * qb + rb;
  // a*b = (m*qa+ra)*(m*qb+rb) = m*(m*qa*qb + qa*rb + qb*ra) + ra*rb
  assert a * b == m * (m * qa * qb + qa * rb + qb * ra) + ra * rb;
  // reorder to ra*rb + m*(...) to use ModAddMulRight
  assert a * b == ra * rb + m * (m * qa * qb + qa * rb + qb * ra);
  // hence (a*b) % m == (ra*rb) % m
  ModAddMulRight(ra * rb, m * qa * qb + qa * rb + qb * ra, m);
  assert (a * b) % m == (ra * rb) % m;
  // and ((a % m) * (b % m)) % m == (ra*rb) % m
  assert ((a % m) * (b % m)) % m == (ra * rb) % m;
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
  var vx := ParseBits(sx);
  var vy := ParseBits(sy);
  var m := ParseBits(sz);
  ParseBitsEqualsStr2Int(sx);
  ParseBitsEqualsStr2Int(sy);
  ParseBitsEqualsStr2Int(sz);
  var resultNat: nat;
  if vy == 0 {
    resultNat := 1 % m;
  } else {
    var cur := vx % m;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant cur < m
      invariant cur == Exp_int(vx, Exp_int(2, i)) % m
      decreases n - i
    {
      // preserve old cur for reasoning
      var oldCur := cur;
      // let aexp = Exp_int(vx, Exp_int(2,i))
      var aexp := Exp_int(vx, Exp_int(2, i));
      // show that Exp_int(vx, Exp_int(2,i+1)) equals aexp*aexp
      Exp_double(vx, i);
      // show modular multiplication compatibility
      ModMulCompatibility(aexp, aexp, m);
      // compute squared remainder
      cur := (oldCur * oldCur) % m;
      // oldCur == aexp % m by invariant
      assert oldCur == aexp % m;
      // so (oldCur*oldCur)%m == ((aexp % m)*(aexp % m))%m
      assert (oldCur * oldCur) % m == ((aexp % m) * (aexp % m)) % m;
      // by ModMulCompatibility this equals (aexp*aexp)%m
      assert ((aexp % m) * (aexp % m)) % m == (aexp * aexp) % m;
      // and by Exp_double aexp*aexp == Exp_int(vx, Exp_int(2,i+1))
      assert (aexp * aexp) % m == Exp_int(vx, Exp_int(2, i + 1)) % m;
      // therefore cur == Exp_int(vx, Exp_int(2,i+1)) % m
      assert cur == Exp_int(vx, Exp_int(2, i + 1)) % m;
      i := i + 1;
    }
    resultNat := cur;
  }
  res := Int2Str(resultNat);
  assert Str2Int(res) == resultNat;
  if vy == 0 {
    assert Exp_int(vx, vy) == 1;
    assert Exp_int(vx, vy) % m == resultNat;
  } else {
    assert vy == Exp_int(2, n);
    assert resultNat == Exp_int(vx, Exp_int(2, n)) % m;
    assert Exp_int(vx, vy) == Exp_int(vx, Exp_int(2, n));
    assert Exp_int(vx, vy) % m == resultNat;
  }
}
// </vc-code>

