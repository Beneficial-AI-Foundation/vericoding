// <vc-preamble>

predicate is_prime(n: int)
{
    n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

function power_of_2_factor(n: int, current: int): int
    requires n > 0 && current > 0
    decreases current
{
    if current % 2 != 0 then 1
    else 2 * power_of_2_factor(n, current / 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Added proof body for the multiplication-division lemma.] */
lemma MulDivides(k: int, c: int)
    requires c != 0
    ensures (k*c) % c == 0
{
    var r := (k*c) % c;
    if r != 0 {
        var q := (k*c)/c;
        assert r == (k-q)*c;

        if c > 0 {
            assert 0 < r < c;
            if k > q {
                assert k-q >= 1;
                assert r >= c;
            } else {
                assert k-q <= -1;
                assert r <= -c;
            }
        } else { // c < 0
            assert 0 < r < -c;
            if k > q {
                assert k-q >= 1;
                assert r <= c;
            } else {
                assert k-q <= -1;
                assert r >= -c;
            }
        }
    }
}

/* helper modified by LLM (iteration 4): [Re-wrote proof using helper lemma to avoid timeout.] */
lemma DividesTransitive(a: int, b: int, c: int)
    requires b != 0
    requires c != 0
    requires a % b == 0
    requires b % c == 0
    ensures a % c == 0
{
    var k1 := a / b;
    var k2 := b / c;
    assert a == k1 * b;
    assert b == k2 * c;
    var k := k1 * k2;
    assert a == k * c;
    MulDivides(k, c);
}

/* helper modified by LLM (iteration 3): [Authored new inductive lemma to prove existence of a prime factor avoiding timeouts.] */
lemma AnyIntegerHasPrimeFactor(m: int)
    requires m > 1
    ensures exists p :: is_prime(p) && m % p == 0 && p <= m
    decreases m
{
    if is_prime(m) {
        assert m % m == 0;
    } else {
        var d :| 1 < d < m && m % d == 0;
        AnyIntegerHasPrimeFactor(d);
        var q :| is_prime(q) && d % q == 0 && q <= d;
        DividesTransitive(m, d, q);
        assert m % q == 0;
        assert q <= d < m;
    }
}

/* helper modified by LLM (iteration 3): [Re-implemented using an inductive helper lemma to fix verification timeout.] */
lemma PrimeFactorOfCompositeExists(n: int)
    requires n > 1 && !is_prime(n)
    ensures exists p :: p > 1 && p < n && is_prime(p) && n % p == 0
{
    AnyIntegerHasPrimeFactor(n);
    var p :| is_prime(p) && n % p == 0 && p <= n;
    
    if p == n {
        assert is_prime(n);
        assert false;
    }
    assert p < n;
    assert p > 1;
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (result: int)
    requires n > 1
    requires !is_prime(n)
    ensures result > 1
    ensures n % result == 0
    ensures forall k :: k > result && n % k == 0 ==> !is_prime(k)
    ensures is_prime(result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [No change; logic is sound pending helper fix.] */
  var i := n - 1;
  while i > 1
    decreases i
    invariant 1 <= i < n
    invariant forall k :: i < k < n && n % k == 0 ==> !is_prime(k)
  {
    if n % i == 0 {
      if is_prime(i) {
        result := i;
        return;
      }
    }
    i := i - 1;
  }
  PrimeFactorOfCompositeExists(n);
  assert false; // This part is unreachable because the loop must find a prime factor
}
// </vc-code>
