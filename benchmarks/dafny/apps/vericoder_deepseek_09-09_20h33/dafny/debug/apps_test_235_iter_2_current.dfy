predicate ValidInput(n: int)
{
    n >= 1
}

function vasya_eats_with_strategy(n: int, k: int): int
    requires n >= 0
    requires k >= 1
    decreases n
{
    if n <= 0 then 0
    else
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        cur + vasya_eats_with_strategy(remaining_after_petya, k)
}

predicate IsMinimalSolution(n: int, k: int)
    requires ValidInput(n)
    requires k >= 1
{
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}

// <vc-helpers>
lemma lemma_div_lt(x: int, y: int, z: int)
  requires x > 0 && y > 0 && z > 0
  requires x * z <= y
  ensures x <= y / z
{
}

lemma lemma_div_ge(x: int, y: int, z: int)
  requires x >= 0 && y >= 0 && z > 0
  requires x * z >= y
  ensures x >= y / z
{
}

lemma lemma_vasya_monotonic_k(n: int, k1: int, k2: int)
  requires n >= 0
  requires 1 <= k1 <= k2
  ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
  decreases n
{
  if n <= 0 {
    return;
  }
  var cur1 := if n < k1 then n else k1;
  var cur2 := if n < k2 then n else k2;
  assert cur1 <= cur2;

  var rem1_vasya := n - cur1;
  var rem2_vasya := n - cur2;
  assert rem1_vasya >= rem2_vasya;

  var rem1_petya := rem1_vasya - rem1_vasya / 10;
  var rem2_petya := rem2_vasya - rem2_vasya / 10;
  
  assert rem1_petya >= rem2_petya;
  
  lemma_vasya_monotonic_k(rem1_petya, k1, k2);
}

lemma lemma_exists_k_strategy(n: int, k: int)
  requires n >= 1
  requires k >= 1 && k <= n
  ensures exists k': int :: k <= k' <= n && vasya_eats_with_strategy(n, k') * 2 >= n
{
  if vasya_eats_with_strategy(n, k) * 2 >= n {
    // k itself satisfies the condition
  } else {
    // For n >= 1, k = n always satisfies: vasya_eats_with_strategy(n, n) = n, so n * 2 >= n
    assert vasya_eats_with_strategy(n, n) == n;
    assert n * 2 >= n;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures 1 <= result <= n
    ensures IsMinimalSolution(n, result)
// </vc-spec>
// <vc-code>
{
  var low := 1;
  var high := n;
  
  // First prove that high satisfies the exists invariant
  assert vasya_eats_with_strategy(n, n) == n;
  assert n * 2 >= n;
  
  while low < high
    invariant 1 <= low <= high <= n
    invariant forall k: int :: 1 <= k < low ==> vasya_eats_with_strategy(n, k) * 2 < n
    invariant exists k: int :: high <= k <= n && vasya_eats_with_strategy(n, k) * 2 >= n
  {
    var mid := low + (high - low) / 2;
    var eats := vasya_eats_with_strategy(n, mid);
    
    if eats * 2 >= n {
      high := mid;
      // The exists invariant is maintained because mid is in [low, high] and satisfies the condition
    } else {
      low := mid + 1;
      // The forall invariant is maintained because all k < mid+1 have strategy < n/2
      // The exists invariant is maintained by the previous high value
    }
  }
  
  result := high;
  // Now prove the postcondition IsMinimalSolution(n, result)
  assert vasya_eats_with_strategy(n, result) * 2 >= n;  // from exists invariant
  if result > 1 {
    // From forall invariant with k = result-1
    assert forall k: int :: 1 <= k < result ==> vasya_eats_with_strategy(n, k) * 2 < n;
    assert vasya_eats_with_strategy(n, result - 1) * 2 < n;
  }
}
// </vc-code>

