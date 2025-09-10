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
  var ans := n; 

  while low <= high
    invariant 1 <= low <= n + 1
    invariant 0 <= high <= n
    invariant 1 <= ans <= n
    invariant (low > high) ==> IsMinimalSolution(n, ans)
    invariant high < n ==> (forall k' :: high < k' <= n ==> vasya_eats_with_strategy(n, k') * 2 < n)
    invariant low > 1 ==> (forall k' :: 1 <= k' < low ==> vasya_eats_with_strategy(n, k') * 2 >= n)
    invariant (vasya_eats_with_strategy(n, ans) * 2 >= n)
  {
    var mid := low + (high - low) / 2;
    assert 1 <= mid <= n;

    if vasya_eats_with_strategy(n, mid) * 2 >= n
    {
      ans := mid;
      high := mid - 1;
    }
    else
    {
      low := mid + 1;
    }
  }
  result := ans;
}
// </vc-code>

