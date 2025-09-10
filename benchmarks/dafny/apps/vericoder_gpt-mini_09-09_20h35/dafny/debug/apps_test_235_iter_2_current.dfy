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
lemma VasyaZeroForZero(k: int)
  requires k >= 1
  ensures vasya_eats_with_strategy(0, k) == 0
{
  // By definition of the function: if n <= 0 then 0
}

lemma VasyaEatsAllWhenKAtLeastN(n: int)
  requires n >= 0
  ensures vasya_eats_with_strategy(n, n) == n
{
  if n == 0 {
    // vasya_eats_with_strategy(0,0) == 0 by definition
  } else {
    // From n >= 0 and n != 0 we get n >= 1, needed to call VasyaZeroForZero
    assert n >= 1;
    // compute cur = if n < n then n else n == n
    assert (if n < n then n else n) == n;
    var cur := if n < n then n else n;
    assert cur == n;
    var remaining_after_vasya := n - cur;
    assert remaining_after_vasya == 0;
    var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
    assert remaining_after_petya == 0;
    // unfold the function once
    assert vasya_eats_with_strategy(n, n) == cur + vasya_eats_with_strategy(remaining_after_petya, n);
    // remaining_after_petya == 0, so vasya_eats_with_strategy(0, n) == 0
    VasyaZeroForZero(n);
    assert vasya_eats_with_strategy(remaining_after_petya, n) == 0;
    assert vasya_eats_with_strategy(n, n) == n;
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
  var k := 1;
  while k <= n && vasya_eats_with_strategy(n, k) * 2 < n
    invariant 1 <= k <= n + 1
    invariant forall j :: 1 <= j < k ==> vasya_eats_with_strategy(n, j) * 2 < n
    decreases n - k + 1
  {
    k := k + 1;
  }
  // Ensure we have a witness for k == n case
  VasyaEatsAllWhenKAtLeastN(n);
  if k > n {
    // If loop reached n+1, pick n (by lemma vasya_eats_with_strategy(n,n) == n, this satisfies the predicate)
    result := n;
  } else {
    result := k;
  }
}
// </vc-code>

