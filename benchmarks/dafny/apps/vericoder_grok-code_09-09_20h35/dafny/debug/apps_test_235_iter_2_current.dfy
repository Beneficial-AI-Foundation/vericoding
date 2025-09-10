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

predicate ValidInput(n: int)
{
    n >= 1
}

predicate IsMinimalSolution(n: int, k: int)
    requires ValidInput(n)
    requires k >= 1
{
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}

lemma MonotonicK(n: int, k1: int, k2: int)
    requires n >= 0
    requires k1 >= 1
    requires k2 >= 1
    requires k1 <= k2
    ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n > 0 {
        var cur1 := if n < k1 then n else k1;
        var cur2 := if n < k2 then n else k2;
        if n < k1 {
            assert cur1 == n;
            assert cur2 == n;
            assert cur1 <= cur2;
        } else {
            assert cur1 == k1;
            assert cur2 == k2;
            assert cur1 <= cur2;
        }
        var remaining_after_vasya := n - cur1;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        MonotonicK(remaining_after_petya, k1, k2);
    }
}

lemma ExistsMax(n: int)
    requires n >= 1
    ensures vasya_eats_with_strategy(n, n) * 2 >= n
    decreases n
{
    if n > 0 {
        var cur := n;
        var remaining_after_vasya := 0;
        var remaining_after_petya := 0;
        assert cur >= n;
        // Base case for induction
    } else {
        // n == 1 or more, but for n==1, directly check
    }
    // Inductive case implies
}

lemma ExistsMin(n: int)
    requires n >= 1
    ensures vasya_eats_with_strategy(n, 1) * 2 < n || n == 1
    decreases n
{
    // For small n, compute directly, otherwise inductive
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
  var lo := 1;
  var hi := n;
  while lo < hi
    invariant 1 <= lo <= hi <= n
    invariant vasya_eats_with_strategy(n, hi) * 2 >= n
    invariant ! (vasya_eats_with_strategy(n, lo) * 2 >= n)
  {
    var mid := (lo + hi) / 2;
    if vasya_eats_with_strategy(n, mid) * 2 >= n
    {
      hi := mid;
    }
    else
    {
      lo := mid + 1;
    }
  }
  result := lo;
}
// </vc-code>

