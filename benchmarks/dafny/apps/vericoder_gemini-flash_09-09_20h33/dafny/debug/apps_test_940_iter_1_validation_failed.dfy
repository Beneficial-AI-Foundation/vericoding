predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

predicate IsTriangle(a: int, b: int, c: int)
{
    a + b > c && a + c > b && b + c > a
}

function MinOperationsNeeded(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var max_val := max(max(a, b), c);
    var sum_of_other_two := a + b + c - max_val;
    max(0, max_val - sum_of_other_two + 1)
}

// <vc-helpers>
function min(a: int, b: int): int {
    if a < b then a else b
}

function max(a: int, b: int): int {
    if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result >= 0
    ensures result == MinOperationsNeeded(a, b, c)
    ensures result == 0 <==> IsTriangle(a, b, c)
// </vc-spec>
// <vc-code>
{
    var max_val := max(max(a, b), c);
    var sum_of_other_two := a + b + c - max_val;

    if IsTriangle(a, b, c) then
        result := 0;
        assert max_val - sum_of_other_two + 1 <= 0; // Proof that MinOperationsNeeded is 0 when IsTriangle is true
    else
        // This calculates max_val - sum_of_other_two + 1, ensuring it's at least 1,
        // because if it's not a triangle, max_val >= sum_of_other_two + 1.
        result := max_val - sum_of_other_two + 1;
        assert result > 0; // Proof that MinOperationsNeeded is > 0 when IsTriangle is false
    
    // Prove result == MinOperationsNeeded(a, b, c)
    // Case 1: IsTriangle(a, b, c)
    //   In this case, result is 0.
    //   By definition of IsTriangle and properties of sums, when a, b, c form a triangle,
    //   max_val < sum_of_other_two.
    //   Specifically, a + b > c, a + c > b, b + c > a.
    //   If max_val = c, then a + b > c implies a + b - c > 0.
    //   sum_of_other_two - max_val = (a + b + c - max_val) - max_val = a + b - c if c is max_val.
    //   Then max_val - sum_of_other_two + 1 = -(a+b-c) + 1. This would be <= 0.
    //   For example, if (3, 4, 5), max_val=5, sum_other=7. MinOperationsNeeded = max(0, 5-7+1) = max(0, -1) = 0.
    //   If (2, 3, 4), max_val=4, sum_other=5. MinOperationsNeeded = max(0, 4-5+1) = max(0, 0) = 0.
    //   So if IsTriangle, max_val - sum_of_other_two + 1 <= 0, thus MinOperationsNeeded will be 0.
    // Case 2: not IsTriangle(a, b, c)
    //   In this case, result is max_val - sum_of_other_two + 1.
    //   By definition of IsTriangle, if it's not a triangle, at least one condition fails.
    //   Without loss of generality, assume a + b <= c. Then max_val must be c.
    //   So c >= a + b.
    //   max_val - sum_of_other_two = c - (a + b) = c - a - b.
    //   Since c >= a + b, then c - a - b >= 0.
    //   So max_val - sum_of_other_two + 1 >= 1.
    //   Thus, max(0, max_val - sum_of_other_two + 1) will be max_val - sum_of_other_two + 1.
    //   This matches result.

    // This handles the `ensures result == MinOperationsNeeded(a, b, c)` and `result == 0 <==> IsTriangle(a, b, c)`
    // by construction and the logic within the if/else branching.
    // The `assert` statements within the branches are conceptual proofs that Dafny's SMT solver can verify.
}
// </vc-code>

