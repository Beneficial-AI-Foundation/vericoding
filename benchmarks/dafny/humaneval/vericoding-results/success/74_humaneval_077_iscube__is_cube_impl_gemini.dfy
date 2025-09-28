// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas to isolate complex proofs and resolve timeout */
lemma lemma_cube_is_monotonic(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
}

lemma lemma_cube_growth(n: nat)
  ensures n > 1 ==> cube(n) >= n
  ensures cube(n + 1) > n
{
}

// This lemma isolates the complex forall proof, which is the likely cause of the timeout.
lemma lemma_forall_not_cube(low: nat, n: nat)
  requires cube(low) < n < cube(low + 1)
  ensures forall r :: 0 <= r <= n ==> n != cube(r)
{
  forall r | 0 <= r <= n
    ensures n != cube(r)
  {
    if r <= low {
      if r < low {
        lemma_cube_is_monotonic(r, low);
      }
      assert cube(r) <= cube(low);
      assert cube(r) < n;
    } else { // r >= low + 1
      if r > low + 1 {
        lemma_cube_is_monotonic(low + 1, r);
      }
      assert cube(r) >= cube(low + 1);
      assert cube(r) > n;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implemented binary search and called helper lemmas for postconditions */
  var low: nat := 0;
  var high: nat := n + 1;

  lemma_cube_growth(n);

  while low < high - 1
    invariant 0 <= low < high <= n + 1
    invariant cube(low) <= n
    invariant n < cube(high)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if cube(mid) <= n {
      low := mid;
    } else {
      high := mid;
    }
  }
  assert high == low + 1;
  assert cube(low) <= n < cube(low + 1);

  if cube(low) == n {
    lemma_cube_growth(low);
    if low > 1 {
        assert cube(low) >= low;
    }
    r := true;
  } else {
    assert cube(low) < n < cube(low + 1);
    lemma_forall_not_cube(low, n);
    r := false;
  }
}
// </vc-code>
