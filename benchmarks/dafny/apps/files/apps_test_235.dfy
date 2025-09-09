Given n candies, find the minimum k such that Vasya eats at least half of the original candies.
Daily process: Vasya eats k candies in morning, Petya eats floor(remaining/10) in evening.
Continue until no candies remain.

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

method can(n: int, k: int) returns (result: bool)
    requires n >= 0
    requires k >= 1
    ensures result <==> (vasya_eats_with_strategy(n, k) * 2 >= n)
{
    var total := n;
    var remaining := n;
    var vasya_sum := 0;

    while remaining > 0
        invariant remaining >= 0
        invariant vasya_sum >= 0
        invariant vasya_sum + vasya_eats_with_strategy(remaining, k) == vasya_eats_with_strategy(total, k)
    {
        var cur := if remaining < k then remaining else k;
        vasya_sum := vasya_sum + cur;
        remaining := remaining - cur;

        remaining := remaining - remaining / 10;
    }

    result := vasya_sum * 2 >= total;
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures 1 <= result <= n
    ensures IsMinimalSolution(n, result)
{
    var le := 0;
    var rg := n;

    while rg - le > 1
        invariant 0 <= le < rg <= n
        invariant le == 0 || vasya_eats_with_strategy(n, le) * 2 < n
        invariant vasya_eats_with_strategy(n, rg) * 2 >= n
    {
        var mid := (rg + le) / 2;
        var canResult := can(n, mid);
        if canResult {
            rg := mid;
        } else {
            le := mid;
        }
    }

    result := rg;
}
