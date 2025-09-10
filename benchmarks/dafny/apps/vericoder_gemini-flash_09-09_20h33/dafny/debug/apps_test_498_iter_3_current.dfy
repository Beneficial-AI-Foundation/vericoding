predicate ValidInput(n: int, m: int, k: int)
{
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

predicate ValidOutput(n: int, m: int, lane: int, desk: int, side: string)
{
    1 <= lane <= n && 1 <= desk <= m && (side == "L" || side == "R")
}

predicate CorrectSolution(n: int, m: int, k: int, lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
}

// <vc-helpers>
lemma lemma_k_minus_1_ge_0(k: int)
    requires k >= 1
    ensures k - 1 >= 0
{}
lemma lemma_division_properties(a: int, b: int)
    requires a >= 0
    requires b > 0
    ensures a == (a / b) * b + (a % b)
{}
lemma lemma_multiplication_associativity(a: int, b: int, c: int)
    ensures (a * b) * c == a * (b * c)
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
    ensures ValidOutput(n, m, lane, desk, side)
    ensures CorrectSolution(n, m, k, lane, desk, side)
// </vc-spec>
// <vc-code>
{
    var k_minus_1 := k - 1;
    lemma_k_minus_1_ge_0(k);
    
    // Prove that 2*m > 0
    assert m >= 1;
    assert 2 * m >= 2;
    
    // Calculate lane
    lane := k_minus_1 / (2 * m) + 1;
    
    // Calculate remainder_2m
    var remainder_2m := k_minus_1 % (2 * m);
    
    // Prove remainder_2m is in the correct range for division by 2
    assert remainder_2m >= 0;
    assert remainder_2m < 2 * m;

    // Calculate desk
    desk := remainder_2m / 2 + 1;
    
    // Determine side
    if remainder_2m % 2 == 0
    {
        side := "L";
    }
    else
    {
        side := "R";
    }

    // Post-condition proofs for CorrectSolution
    // 1. lane == (k - 1) / (2 * m) + 1
    assert lane == (k - 1) / (2 * m) + 1;

    // 2. desk == (k - 1) % (2 * m) / 2 + 1
    lemma_division_properties(k_minus_1, 2 * m);
    assert k_minus_1 == (k_minus_1 / (2 * m)) * (2 * m) + (k_minus_1 % (2 * m));
    assert remainder_2m == (k - 1) % (2 * m);
    assert desk == (k - 1) % (2 * m) / 2 + 1;

    // 3. (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
    assert (remainder_2m % 2 == 0) <==> (side == "L");
    assert ((k - 1) % (2 * m) % 2 == 0) <==> (side == "L");

    // Post-condition proofs for ValidOutput
    // 1. 1 <= lane <= n
    assert 2 * m >= 2;
    assert k >= 1;
    assert k <= 2 * n * m;
    assert k_minus_1 >= 0;
    assert k_minus_1 <= 2 * n * m - 1;
    assert k_minus_1 / (2 * m) <= (2 * n * m - 1) / (2 * m);
    assert (2 * n * m - 1) / (2 * m) == n - 1; // Since 2*m > 0, this holds.
    assert (k_minus_1 / (2 * m)) <= n - 1;
    assert lane == (k_minus_1 / (2 * m)) + 1;
    assert lane <= n - 1 + 1;
    assert lane <= n;
    assert lane >= 1; // Since k_minus_1 / (2*m) >= 0

    // 2. 1 <= desk <= m
    assert remainder_2m >= 0;
    assert remainder_2m < 2 * m;
    assert remainder_2m / 2 < m;
    assert remainder_2m / 2 >= 0;
    assert desk == remainder_2m / 2 + 1;
    assert desk <= m - 1 + 1;
    assert desk <= m;
    assert desk >= 1; // Since remainder_2m / 2 >= 0

    // 3. (side == "L" || side == "R")
    assert side == "L" || side == "R";
}
// </vc-code>

