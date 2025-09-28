// <vc-preamble>

function abs(x: int): nat
{
    if x >= 0 then x else -x
}

predicate divides(d: int, n: int)
{
    if d == 0 then n == 0 else n % d == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): gcd function (Euclidean) */
function gcd(x: nat, y: nat): nat
  decreases y
{
  if y == 0 then x else gcd(y, x % y)
}

/* helper modified by LLM (iteration 5): gcd zero characterization */
lemma GcdZero(x: nat, y: nat)
  ensures gcd(x,y) == 0 <==> (x == 0 && y == 0)
  decreases y
{
  if y == 0 {
    assert gcd(x,0) == x;
    assert (gcd(x,0) == 0) <==> (x == 0);
  } else {
    assert gcd(x,y) == gcd(y, x % y);
    GcdZero(y, x % y);
    assert (gcd(x,y) == 0) <==> (x == 0 && y == 0);
  }
}

/* helper modified by LLM (iteration 5): gcd divides both arguments */
lemma GcdDivides(x: nat, y: nat)
  ensures divides(gcd(x,y), x) && divides(gcd(x,y), y)
  decreases y
{
  if y == 0 {
    assert gcd(x, 0) == x;
    assert divides(x, x);
    assert divides(x, 0);
  } else {
    var g := gcd(x, y);
    assert g == gcd(y, x % y);
    GcdDivides(y, x % y);
    // from recursive call: divides(g, y) && divides(g, x % y)
    assert divides(g, y);
    assert divides(g, x % y);
    var q := x / y;
    assert x == q * y + x % y;
    // combine divisibility facts to conclude divides(g, x)
    // if g == 0 then y == 0, which contradicts else-branch, so g > 0 here
    if g == 0 {
      // unreachable when y != 0, but keep for completeness
      assert x == 0;
    } else {
      var t := y / g;
      assert y == t * g;
      var u := (x % y) / g;
      assert x % y == u * g;
      assert x == (q * t + u) * g;
      assert x % g == 0;
    }
  }
}

/* helper modified by LLM (iteration 5): gcd is greatest common divisor */
lemma GcdGreatest(x: nat, y: nat)
  ensures forall d: int :: d > 0 && divides(d, x) && divides(d, y) ==> d <= gcd(x,y)
  decreases y
{
  if y == 0 {
    assert gcd(x, 0) == x;
    forall d | d > 0 && divides(d, x) && divides(d, 0) {
      if x == 0 {
        assert d <= x;
      } else {
        var k := x / d;
        assert x == k * d;
        assert k >= 1;
        assert d <= x;
      }
    }
  } else {
    var g := gcd(x, y);
    assert g == gcd(y, x % y);
    GcdGreatest(y, x % y);
    forall d | d > 0 && divides(d, x) && divides(d, y) {
      // show divides(d, x % y) by direct arithmetic
      var t := y / d;
      assert y == t * d;
      var s := x / d;
      assert x == s * d;
      var q := x / y;
      var r := x % y;
      assert x == q * y + r;
      assert q * y == (q * t) * d;
      assert r == (s - q * t) * d;
      assert divides(d, r);
      assert divides(d, x % y);
      assert d <= gcd(y, x % y);
      assert d <= g;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (result: nat)
    ensures result > 0 <==> (a != 0 || b != 0)
    ensures result == 0 <==> (a == 0 && b == 0)
    ensures divides(result, a) && divides(result, b)
    ensures forall d: int :: d > 0 && divides(d, a) && divides(d, b) ==> d <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute gcd of absolute values and discharge postconditions using lemmas */
  var x := abs(a);
  var y := abs(b);
  result := gcd(x, y);
  GcdZero(x, y);
  GcdDivides(x, y);
  GcdGreatest(x, y);
}

// </vc-code>
