// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): refined proof for multiples of 11 in [0,10] implying zero */
lemma NonNegMultipleOf11LessThan11ImpliesZero(t: int)
  ensures 0 <= 11 * t < 11 ==> t == 0
{
  if 0 <= 11 * t < 11 {
    if t <= -1 {
      assert 11 * t <= -11;
      assert 0 <= 11 * t;
      assert false;
    } else if t >= 1 {
      assert 11 * t >= 11;
      assert 11 * t < 11;
      assert false;
    } else {
      assert 0 <= t;
      assert t <= 0;
      assert t == 0;
    }
  }
}

/* helper modified by LLM (iteration 3): provide explicit witness and tighten arithmetic reasoning */
lemma DividesIffRemainderZero11(n: int)
  ensures (n % 11 == 0) <==> (exists k: int :: k * 11 == n)
{
  if n % 11 == 0 {
    var q := n / 11;
    assert n == 11 * q + n % 11;
    assert n == 11 * q;
    assert exists k: int :: k * 11 == n by {
      assert q * 11 == 11 * q;
      assert q * 11 == n;
    }
  }
  if exists k: int :: k * 11 == n {
    var kWitness :| kWitness * 11 == n;
    assert 11 * kWitness == kWitness * 11;
    assert 11 * kWitness == n;
    assert n == 11 * (n / 11) + n % 11;
    assert n - 11 * (n / 11) == n % 11;
    var t := kWitness - (n / 11);
    assert 11 * t == 11 * kWitness - 11 * (n / 11);
    assert 11 * t == n - 11 * (n / 11);
    assert 11 * t == n % 11;
    assert 0 <= n % 11 < 11;
    assert 0 <= 11 * t < 11;
    NonNegMultipleOf11LessThan11ImpliesZero(t);
    assert t == 0;
    assert n % 11 == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute by remainder and appeal to helper equivalence */
  result := n % 11 == 0;
  DividesIffRemainderZero11(n);
}
// </vc-code>
