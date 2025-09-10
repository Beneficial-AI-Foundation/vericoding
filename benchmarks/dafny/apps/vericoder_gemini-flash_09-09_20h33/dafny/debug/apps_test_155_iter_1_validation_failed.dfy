predicate ValidInput(n: int, m: int, k: int) {
    n >= 2 && m >= 2 && n % 2 == 0 && k >= 0 && k < n * m
}

predicate ValidOutput(result: seq<int>, n: int, m: int) {
    |result| == 2 && result[0] >= 1 && result[0] <= n && result[1] >= 1 && result[1] <= m
}

predicate CorrectPosition(result: seq<int>, n: int, m: int, k: int) 
    requires ValidInput(n, m, k)
    requires |result| == 2
{
    if k < n then
        result[0] == k + 1 && result[1] == 1
    else
        var k_remaining := k - n;
        var r := n - k_remaining / (m - 1);
        result[0] == r &&
        (r % 2 == 1 ==> result[1] == m - k_remaining % (m - 1)) &&
        (r % 2 == 0 ==> result[1] == 2 + k_remaining % (m - 1))
}

// <vc-helpers>
function Modulo(a: int, b: int): int
    requires b > 0
    ensures 0 <= Modulo(a, b) < b
{
    var r := a % b;
    if r < 0 then r + b else r
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, m, k)
    ensures ValidOutput(result, n, m)
    ensures CorrectPosition(result, n, m, k)
// </vc-spec>
// <vc-code>
{
    var row: int;
    var col: int;

    if k < n {
        row := k + 1;
        col := 1;
    } else {
        var k_remaining := k - n;
        var num_cols_minus_1 := m - 1;

        if num_cols_minus_1 == 0 { // This case implies m=1, but m >= 2 from ValidInput
            // This 'if' branch should theoretically not be reachable due to the `m >= 2`
            // precondition, but Dafny might require an explicit handling or proof.
            // Given m >= 2, num_cols_minus_1 must be >= 1.
            // If m=1 were allowed, k_remaining / (m-1) would be division by zero.
            // Since the problem statement guarantees m >= 2, this branch is unreachable.
            // We can place placeholder values or an unreachable assertion if needed,
            // but for simplicity, we assume the precondition holds and eliminates this path.
            row := 1; // Placeholder
            col := 1; // Placeholder
        } else {
            var full_sweeps := k_remaining / num_cols_minus_1;
            var sub_sweep_remainder := Modulo(k_remaining, num_cols_minus_1);

            row := n - full_sweeps;

            if row % 2 == 1 { // Odd row number, sweeping right to left
                col := m - sub_sweep_remainder;
            } else { // Even row number, sweeping left to right
                col := 2 + sub_sweep_remainder;
            }
        }
    }

    result := [row, col];
}
// </vc-code>

