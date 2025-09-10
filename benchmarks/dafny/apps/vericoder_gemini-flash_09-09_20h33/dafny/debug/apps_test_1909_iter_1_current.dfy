predicate ValidInput(n: int, k: int, powers: seq<int>)
{
    n > 0 && k > 0 && k <= n && n % k == 0 && |powers| == n
}

predicate IsOptimalStartingTask(result: int, n: int, k: int, powers: seq<int>)
    requires ValidInput(n, k, powers)
{
    1 <= result <= k
}

// <vc-helpers>
function get_sum_of_powers_for_starting_task(powers: seq<int>, starting_task: int, n: int, k: int): int
    requires ValidInput(n, k, powers)
    requires 1 <= starting_task <= k
    ensures 0 <= get_sum_of_powers_for_starting_task(powers, starting_task, n, k)
{
    var sum := 0;
    var i := starting_task - 1;
    while i < n
        invariant 0 <= i <= n
        invariant sum == (if i >= starting_task - 1 then sum(powers[starting_task - 1 .. i]) else 0)
    {
        sum := sum + powers[i];
        i := i + k;
    }
    return sum;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, powers: seq<int>) returns (result: int)
    requires ValidInput(n, k, powers)
    ensures IsOptimalStartingTask(result, n, k, powers)
// </vc-spec>
// <vc-code>
{
    var min_sum := -1;
    var optimal_task := -1;

    for i := 1 to k
        invariant 1 <= i <= k + 1
        invariant optimal_task == -1 || (1 <= optimal_task <= i - 1)
        invariant optimal_task != -1 ==> min_sum == get_sum_of_powers_for_starting_task(powers, optimal_task, n, k)
        invariant forall j :: 1 <= j < i && optimal_task != -1 ==> get_sum_of_powers_for_starting_task(powers, j, n, k) >= min_sum
    {
        var current_sum := get_sum_of_powers_for_starting_task(powers, i, n, k);
        if optimal_task == -1 || current_sum < min_sum {
            min_sum := current_sum;
            optimal_task := i;
        }
    }
    return optimal_task;
}
// </vc-code>

