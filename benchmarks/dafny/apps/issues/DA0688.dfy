// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, c: int)
{
    1 <= n <= 1000000000 && 1 <= a <= 1000000000 && 1 <= b <= 1000000000 && 1 <= c <= 1000000000
}

predicate ValidSolution(n: int, a: int, b: int, c: int, result: int)
{
    result >= 0 &&
    (exists i, j, k :: 0 <= i < 50 && 0 <= j < 50 && 0 <= k < 50 && 
        (n + i + 2 * j + 3 * k) % 4 == 0 && result == a * i + b * j + c * k)
}

predicate OptimalSolution(n: int, a: int, b: int, c: int, result: int)
{
    forall i, j, k :: (0 <= i < 50 && 0 <= j < 50 && 0 <= k < 50 && 
        (n + i + 2 * j + 3 * k) % 4 == 0) ==> result <= a * i + b * j + c * k
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, c: int) returns (result: int)
    requires ValidInput(n, a, b, c)
    ensures ValidSolution(n, a, b, c, result)
    ensures OptimalSolution(n, a, b, c, result)
// </vc-spec>
// <vc-code>
{
    // Find explicit witness based on n % 4
    var witness_i, witness_j, witness_k: int;
    var n_mod := n % 4;

    if n_mod == 0 {
        witness_i, witness_j, witness_k := 0, 0, 0;
    } else if n_mod == 1 {
        witness_i, witness_j, witness_k := 3, 0, 0;
    } else if n_mod == 2 {
        witness_i, witness_j, witness_k := 2, 0, 0;
    } else { // n_mod == 3
        witness_i, witness_j, witness_k := 1, 0, 0;
    }

    // Verify our witness works
    assert (n + witness_i + 2 * witness_j + 3 * witness_k) % 4 == 0;

    // Now find the minimum cost solution
    var res := a * witness_i + b * witness_j + c * witness_k;
    var best_i, best_j, best_k := witness_i, witness_j, witness_k;

    var i := 0;
    while i < 50
        invariant 0 <= i <= 50
        invariant 0 <= best_i < 50 && 0 <= best_j < 50 && 0 <= best_k < 50
        invariant (n + best_i + 2 * best_j + 3 * best_k) % 4 == 0 
        invariant res == a * best_i + b * best_j + c * best_k
        invariant forall ii, jj, kk :: (0 <= ii < i && 0 <= jj < 50 && 0 <= kk < 50 && 
                (n + ii + 2 * jj + 3 * kk) % 4 == 0) ==> res <= a * ii + b * jj + c * kk
        invariant res >= 0
    {
        var j := 0;
        while j < 50
            invariant 0 <= j <= 50
            invariant 0 <= best_i < 50 && 0 <= best_j < 50 && 0 <= best_k < 50
            invariant (n + best_i + 2 * best_j + 3 * best_k) % 4 == 0 
            invariant res == a * best_i + b * best_j + c * best_k
            invariant forall ii, jj, kk :: (0 <= ii < i && 0 <= jj < 50 && 0 <= kk < 50 && 
                    (n + ii + 2 * jj + 3 * kk) % 4 == 0) ==> res <= a * ii + b * jj + c * kk
            invariant forall jj, kk :: (0 <= jj < j && 0 <= kk < 50 && 
                    (n + i + 2 * jj + 3 * kk) % 4 == 0) ==> res <= a * i + b * jj + c * kk
            invariant res >= 0
        {
            var k := 0;
            while k < 50
                invariant 0 <= k <= 50
                invariant 0 <= best_i < 50 && 0 <= best_j < 50 && 0 <= best_k < 50
                invariant (n + best_i + 2 * best_j + 3 * best_k) % 4 == 0 
                invariant res == a * best_i + b * best_j + c * best_k
                invariant forall ii, jj, kk :: (0 <= ii < i && 0 <= jj < 50 && 0 <= kk < 50 && 
                        (n + ii + 2 * jj + 3 * kk) % 4 == 0) ==> res <= a * ii + b * jj + c * kk
                invariant forall jj, kk :: (0 <= jj < j && 0 <= kk < 50 && 
                        (n + i + 2 * jj + 3 * kk) % 4 == 0) ==> res <= a * i + b * jj + c * kk
                invariant forall kk :: (0 <= kk < k && 
                        (n + i + 2 * j + 3 * kk) % 4 == 0) ==> res <= a * i + b * j + c * kk
                invariant res >= 0
            {
                if (n + i + 2 * j + 3 * k) % 4 == 0 {
                    var cost := a * i + b * j + c * k;
                    if cost < res {
                        res := cost;
                        best_i, best_j, best_k := i, j, k;
                    }
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    result := res;
}
// </vc-code>
