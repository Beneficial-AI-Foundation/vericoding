// <vc-preamble>

function power(base: int, exp: nat): int
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): PowerPred proves unfolding of power for positive exponent */
lemma PowerPred(a: int, k: nat)
  ensures k > 0 ==> power(a, k) == a * power(a, k-1)
{
  if k > 0 {
    assert power(a, k) == a * power(a, k-1);
  }
}

/* helper modified by LLM (iteration 2): PowerAdd by induction on y: power(a, x+y) = power(a,x)*power(a,y) */
lemma PowerAdd(a: int, x: nat, y: nat)
  ensures power(a, x+y) == power(a, x) * power(a, y)
{
  if y == 0 {
    // power(a, x+0) == power(a, x) * power(a, 0)
    assert power(a, x+0) == power(a, x) * power(a, 0);
  } else {
    // induction on y
    PowerAdd(a, x, y-1);
    // unfold definition for power at x+y
    assert power(a, x+y) == a * power(a, x+y-1);
    // use IH: power(a, x+y-1) == power(a,x) * power(a,y-1)
    assert power(a, x+y-1) == power(a, x) * power(a, y-1);
    // rearrange to reach desired form
    assert a * (power(a, x) * power(a, y-1)) == power(a, x) * (a * power(a, y-1));
    assert a * power(a, y-1) == power(a, y);
    assert power(a, x) * power(a, y) == power(a, x) * (a * power(a, y-1));
    assert power(a, x+y) == power(a, x) * power(a, y);
  }
}

/* helper modified by LLM (iteration 2): PowerBaseMul by induction on k: power(a*c,k) = power(a,k)*power(c,k) */
lemma PowerBaseMul(a: int, c: int, k: nat)
  ensures power(a*c, k) == power(a, k) * power(c, k)
{
  if k == 0 {
    // both sides are 1
    assert power(a*c, 0) == 1;
    assert power(a, 0) * power(c, 0) == 1;
  } else {
    // induction
    PowerBaseMul(a, c, k-1);
    // unfold definitions
    assert power(a*c, k) == (a*c) * power(a*c, k-1);
    assert power(a*c, k-1) == power(a, k-1) * power(c, k-1);
    // substitute and regroup
    assert power(a*c, k) == (a*c) * (power(a, k-1) * power(c, k-1));
    assert (a*c) * (power(a, k-1) * power(c, k-1)) == (a * power(a, k-1)) * (c * power(c, k-1));
    assert a * power(a, k-1) == power(a, k);
    assert c * power(c, k-1) == power(c, k);
    assert (a * power(a, k-1)) * (c * power(c, k-1)) == power(a, k) * power(c, k);
    assert power(a*c, k) == power(a, k) * power(c, k);
  }
}

// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (result: int)
    requires n >= 0 && p > 0
    ensures result >= 0 && result < p
    ensures result == power(2, n) % p
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Implement fast exponentiation and mod reduction without axioms */
  var res: nat := 1;
  var b: nat := 2;
  var e: nat := n;
  while e > 0
    invariant res >= 1
    invariant b >= 1
    invariant res * power(b, e) == power(2, n)
    decreases e
  {
    if e % 2 == 1 {
      var olde := e;
      var oldb := b;
      var oldres := res;
      PowerPred(oldb, olde);
      // update for odd exponent: multiply result by base and decrement exponent
      res := res * b;
      e := e - 1;
      // show invariant preserved
      assert oldres * power(oldb, olde) == power(2, n);
      assert power(oldb, olde) == oldb * power(oldb, olde - 1);
      assert res * power(b, e) == oldres * (oldb * power(oldb, olde - 1));
      assert res * power(b, e) == power(2, n);
    } else {
      var olde := e;
      var oldb := b;
      b := b * b;
      e := e / 2;
      // even exponent: square the base and halve the exponent
      assert olde == 2 * e;
      PowerBaseMul(oldb, oldb, e);
      PowerAdd(oldb, e, e);
      assert power(b, e) == power(oldb, olde);
      assert res * power(b, e) == res * power(oldb, olde);
      assert res * power(oldb, olde) == power(2, n);
    }
  }
  result := res % p;
}

// </vc-code>
