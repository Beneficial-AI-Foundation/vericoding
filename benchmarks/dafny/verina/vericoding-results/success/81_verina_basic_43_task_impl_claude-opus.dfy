// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
function SumOfFourthPowerOfOddNumbers(n: nat): nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    if n == 0 then 0
    else SumOfFourthPowerOfOddNumbers(n-1) + Power4(2*n - 1)
    // impl-end
}

function Power4(x: nat): nat
{
    x * x * x * x
}

lemma SumOfFourthPowerOfOddNumbersSpec(n: nat)
    ensures
        15 * SumOfFourthPowerOfOddNumbers(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
    if n == 0 {
        assert 15 * SumOfFourthPowerOfOddNumbers(0) == 0;
        assert 0 * (2 * 0 + 1) * (7 + 24 * (0 * 0 * 0) - 12 * (0 * 0) - 14 * 0) == 0;
    } else {
        SumOfFourthPowerOfOddNumbersSpec(n-1);
        var prev := SumOfFourthPowerOfOddNumbers(n-1);
        var curr := SumOfFourthPowerOfOddNumbers(n);
        assert curr == prev + Power4(2*n - 1);
        
        calc == {
            15 * curr;
            15 * (prev + Power4(2*n - 1));
            15 * prev + 15 * Power4(2*n - 1);
            { assert 15 * prev == (n-1) * (2 * (n-1) + 1) * (7 + 24 * ((n-1) * (n-1) * (n-1)) - 12 * ((n-1) * (n-1)) - 14 * (n-1)); }
            (n-1) * (2*n - 1) * (7 + 24 * ((n-1) * (n-1) * (n-1)) - 12 * ((n-1) * (n-1)) - 14 * (n-1)) + 15 * Power4(2*n - 1);
        }
        
        var oddNum := 2*n - 1;
        assert Power4(oddNum) == oddNum * oddNum * oddNum * oddNum;
        
        calc == {
            n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n);
            n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7);
        }
        
        AlgebraicExpansion(n);
    }
}

lemma AlgebraicExpansion(n: nat)
    requires n > 0
    ensures 15 * Power4(2*n - 1) + (n-1) * (2*n - 1) * (7 + 24 * ((n-1) * (n-1) * (n-1)) - 12 * ((n-1) * (n-1)) - 14 * (n-1)) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
{
    var oddNum := 2*n - 1;
    assert oddNum * oddNum == 4*n*n - 4*n + 1;
    assert oddNum * oddNum * oddNum == 8*n*n*n - 12*n*n + 6*n - 1;
    assert oddNum * oddNum * oddNum * oddNum == 16*n*n*n*n - 32*n*n*n + 24*n*n - 8*n + 1;
    assert 15 * Power4(oddNum) == 240*n*n*n*n - 480*n*n*n + 360*n*n - 120*n + 15;
    
    var lhs1 := (n-1) * (2*n - 1) * (7 + 24 * ((n-1) * (n-1) * (n-1)) - 12 * ((n-1) * (n-1)) - 14 * (n-1));
    var rhs := n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n);
    
    assert (n-1)*(n-1) == n*n - 2*n + 1;
    assert (n-1)*(n-1)*(n-1) == n*n*n - 3*n*n + 3*n - 1;
    
    assert lhs1 + 15 * Power4(oddNum) == rhs;
}
// </vc-code>
