// <vc-preamble>
ghost function CountArraysWithSumDivisibleBy3(n: int, l: int, r: int): int
    requires n >= 1
    requires l <= r
{
    CountArraysWithSumDivisibleBy3Helper(n, l, r) % 1000000007
}

ghost function CountArraysWithSumDivisibleBy3Helper(n: int, l: int, r: int): int
    requires n >= 0
    requires l <= r
    decreases n
{
    if n == 0 then
        1
    else
        SumOverArrays(n, l, r, 0)
}

ghost function SumOverArrays(n: int, l: int, r: int, target_remainder: int): int
    requires n >= 0
    requires l <= r
    requires 0 <= target_remainder < 3
    decreases n
{
    if n == 0 then
        if target_remainder == 0 then 1 else 0
    else
        var count0 := CountNumsWithRemainder(l, r, 0);
        var count1 := CountNumsWithRemainder(l, r, 1);
        var count2 := CountNumsWithRemainder(l, r, 2);

        var sum_rem0 := count0 * SumOverArrays(n-1, l, r, (target_remainder - 0 + 3) % 3);
        var sum_rem1 := count1 * SumOverArrays(n-1, l, r, (target_remainder - 1 + 3) % 3);
        var sum_rem2 := count2 * SumOverArrays(n-1, l, r, (target_remainder - 2 + 3) % 3);
        sum_rem0 + sum_rem1 + sum_rem2
}

ghost function CountNumsWithRemainder(l: int, r: int, remainder: int): int
    requires l <= r
    requires 0 <= remainder < 3
{
    var total := r - l + 1;
    var cycles := total / 3;
    var remaining := total % 3;
    var first_remainder := l % 3;

    var result := cycles;

    if remaining > 0 && first_remainder == remainder then
        result + 1
    else if remaining > 1 && (first_remainder + 1) % 3 == remainder then
        result + 1
    else if remaining > 2 && (first_remainder + 2) % 3 == remainder then
        result + 1
    else
        result
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, l: int, r: int) returns (result: int)
    requires 1 <= n <= 200000
    requires 1 <= l <= r <= 1000000000
    ensures 0 <= result < 1000000007
    ensures result == CountArraysWithSumDivisibleBy3(n, l, r)
// </vc-spec>
// <vc-code>
{
    var MOD := 1000000007;

    var lr_counts := new int[3];
    var total := r - l + 1;
    var cycles := total / 3;
    var remaining := total % 3;
    var first_remainder := l % 3;

    lr_counts[0] := cycles;
    lr_counts[1] := cycles;
    lr_counts[2] := cycles;

    if remaining > 0 {
        lr_counts[first_remainder] := lr_counts[first_remainder] + 1;
    }
    if remaining > 1 {
        lr_counts[(first_remainder + 1) % 3] := lr_counts[(first_remainder + 1) % 3] + 1;
    }
    if remaining > 2 {
        lr_counts[(first_remainder + 2) % 3] := lr_counts[(first_remainder + 2) % 3] + 1;
    }

    assert lr_counts[0] == CountNumsWithRemainder(l, r, 0);
    assert lr_counts[1] == CountNumsWithRemainder(l, r, 1);
    assert lr_counts[2] == CountNumsWithRemainder(l, r, 2);

    var cur_counts := new int[3];
    cur_counts[0] := 1;
    cur_counts[1] := 0;
    cur_counts[2] := 0;

    var pos := 0;
    while pos < n
        invariant 0 <= pos <= n
        invariant 0 <= cur_counts[0] < MOD
        invariant 0 <= cur_counts[1] < MOD
        invariant 0 <= cur_counts[2] < MOD
        invariant cur_counts[0] == SumOverArrays(pos, l, r, 0) % MOD
        invariant cur_counts[1] == SumOverArrays(pos, l, r, 1) % MOD
        invariant cur_counts[2] == SumOverArrays(pos, l, r, 2) % MOD
    {
        var new_counts := new int[3];
        new_counts[0] := 0;
        new_counts[1] := 0;
        new_counts[2] := 0;

        var j := 0;
        while j < 3
            invariant 0 <= j <= 3
            invariant 0 <= new_counts[0] < MOD
            invariant 0 <= new_counts[1] < MOD
            invariant 0 <= new_counts[2] < MOD
        {
            var k := 0;
            while k < 3
                invariant 0 <= k <= 3
                invariant 0 <= new_counts[0] < MOD
                invariant 0 <= new_counts[1] < MOD
                invariant 0 <= new_counts[2] < MOD
            {
                var new_rem := (j + k) % 3;
                var product := (cur_counts[j] * lr_counts[k]) % MOD;
                assert 0 <= product < MOD;
                new_counts[new_rem] := (new_counts[new_rem] + product) % MOD;
                assert 0 <= new_counts[new_rem] < MOD;
                k := k + 1;
            }
            j := j + 1;
        }

        cur_counts[0] := new_counts[0];
        cur_counts[1] := new_counts[1];
        cur_counts[2] := new_counts[2];

        pos := pos + 1;
    }

    result := cur_counts[0];
    assert 0 <= result < MOD;
    assert result == SumOverArrays(n, l, r, 0) % MOD;
    assert result == CountArraysWithSumDivisibleBy3Helper(n, l, r) % MOD;
    assert result == CountArraysWithSumDivisibleBy3(n, l, r);
}
// </vc-code>
