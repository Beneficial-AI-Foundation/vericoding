// <vc-preamble>
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Search2PowLoop( a: array<int>, i: int, n: int, x: int ) returns ( k: int )
    requires 0 <= i <= i+n <= a.Length;
    requires forall p,q | i <= p < q < i+n :: a[p] <= a[q];
    requires Is2Pow(n+1);
    ensures i <= k <= i+n;
    ensures forall r | i <= r < k :: a[r] < x;
    ensures forall r | k <= r < i+n :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
  var k := i;
  var step := n + 1;

  Is2Pow_is_pow2_lemma(step);

  while step > 1
    decreases step;
    invariant Is2Pow(step);
    invariant 0 < step <= n + 1;
    invariant i <= k <= i + n;
    invariant sorted: forall p, q | i <= p < q < i + n :: a[p] <= a[q];
    invariant k_range: forall r | i <= r < k :: a[r] < x;
    invariant k_updates_by_step: exists m: int :: k - i == m * (step);
    invariant upper_bound: forall r | k + step <= r < i + n :: a[r] >= x;
  {
    assert step % 2 == 0;
    var half_step := step / 2;
    Is2Pow_n_div_2_lemma(step);

    var probe_idx := k + half_step - 1;
    if probe_idx < i + n && a[probe_idx] < x {
      k := k + half_step;
    }
  }
  return k;
}
// </vc-code>
