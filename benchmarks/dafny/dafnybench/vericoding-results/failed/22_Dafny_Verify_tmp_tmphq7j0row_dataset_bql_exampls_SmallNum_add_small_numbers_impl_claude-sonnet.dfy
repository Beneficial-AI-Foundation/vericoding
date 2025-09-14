

// <vc-helpers>
lemma sum_bound(a: array<int>, n: int, max: int, current_sum: int, i: int)
    requires 0 <= i <= n <= a.Length
    requires forall j :: 0 <= j < n ==> a[j] <= max
    requires current_sum == sum_range(a, 0, i)
    ensures current_sum + sum_range(a, i, n) <= max * n
    decreases n - i
{
    if i == n {
        assert sum_range(a, i, n) == 0;
        sum_range_bounded(a, 0, i, max);
        assert current_sum <= max * i;
        assert i <= n;
        assert max * i <= max * n;
    } else {
        assert sum_range(a, i, n) == a[i] + sum_range(a, i + 1, n);
        assert a[i] <= max;
        assert current_sum + a[i] == sum_range(a, 0, i + 1) by {
            sum_range_additive(a, 0, i, i + 1);
        }
        sum_bound(a, n, max, current_sum + a[i], i + 1);
    }
}

lemma sum_range_bounded(a: array<int>, start: int, end: int, max: int)
    requires 0 <= start <= end <= a.Length
    requires forall j :: start <= j < end ==> a[j] <= max
    ensures sum_range(a, start, end) <= max * (end - start)
    decreases end - start
{
    if start == end {
        assert sum_range(a, start, end) == 0;
        assert max * (end - start) == 0;
    } else {
        assert a[start] <= max;
        sum_range_bounded(a, start + 1, end, max);
        assert sum_range(a, start + 1, end) <= max * (end - start - 1);
        assert sum_range(a, start, end) == a[start] + sum_range(a, start + 1, end);
        assert a[start] + sum_range(a, start + 1, end) <= max + max * (end - start - 1);
        assert max + max * (end - start - 1) == max * (end - start);
    }
}

function sum_range(a: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= a.Length
    reads a
    decreases end - start
{
    if start == end then 0
    else a[start] + sum_range(a, start + 1, end)
}

lemma sum_range_additive(a: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= a.Length
    ensures sum_range(a, i, k) == sum_range(a, i, j) + sum_range(a, j, k)
    decreases j - i
{
    if i == j {
        assert sum_range(a, i, j) == 0;
    } else {
        sum_range_additive(a, i + 1, j, k);
    }
}

lemma sum_range_step(a: array<int>, start: int, end: int)
    requires 0 <= start < end <= a.Length
    ensures sum_range(a, start, end) == sum_range(a, start, end - 1) + a[end - 1]
    decreases end - start
{
    if start == end - 1 {
        assert sum_range(a, start, end - 1) == 0;
    } else {
        sum_range_step(a, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
    r := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant r == sum_range(a, 0, i)
        invariant r <= max * i
    {
        assert a[i] <= max;
        assert r + a[i] <= max * i + max;
        assert max * i + max == max * (i + 1);
        
        r := r + a[i];
        i := i + 1;
        
        sum_range_step(a, 0, i);
    }
    
    assert i == n;
    assert r == sum_range(a, 0, n);
    assert r <= max * n;
}
// </vc-code>

