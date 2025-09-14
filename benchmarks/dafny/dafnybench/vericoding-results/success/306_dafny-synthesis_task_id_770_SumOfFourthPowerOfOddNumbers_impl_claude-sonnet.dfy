

// <vc-helpers>
lemma SumOfFourthPowerHelper(k: int)
    requires k >= 0
    ensures SumOfOddFourthPowers(k) == k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15
{
    if k == 0 {
        assert SumOfOddFourthPowers(0) == 0;
        assert 0 * (2 * 0 + 1) * (24 * 0 * 0 * 0 - 12 * 0 * 0 - 14 * 0 + 7) / 15 == 0;
    } else {
        SumOfFourthPowerHelper(k - 1);
        calc {
            SumOfOddFourthPowers(k);
            == SumOfOddFourthPowers(k - 1) + Pow4(2 * k - 1);
            == (k - 1) * (2 * (k - 1) + 1) * (24 * (k - 1) * (k - 1) * (k - 1) - 12 * (k - 1) * (k - 1) - 14 * (k - 1) + 7) / 15 + Pow4(2 * k - 1);
        }
        
        var prev_term := (k - 1) * (2 * (k - 1) + 1) * (24 * (k - 1) * (k - 1) * (k - 1) - 12 * (k - 1) * (k - 1) - 14 * (k - 1) + 7) / 15;
        var current_term := Pow4(2 * k - 1);
        var expected := k * (2 * k + 1) * (24 * k * k * k - 12 * k * k - 14 * k + 7) / 15;
        
        assert prev_term + current_term == expected by {
            calc {
                current_term;
                == Pow4(2 * k - 1);
                == (2 * k - 1) * (2 * k - 1) * (2 * k - 1) * (2 * k - 1);
            }
            
            var expanded_prev := (k - 1) * (2 * k - 1) * (24 * (k - 1) * (k - 1) * (k - 1) - 12 * (k - 1) * (k - 1) - 14 * (k - 1) + 7) / 15;
            var expanded_current := (2 * k - 1) * (2 * k - 1) * (2 * k - 1) * (2 * k - 1);
            
            assert prev_term == expanded_prev;
            assert current_term == expanded_current;
            assert expanded_prev + expanded_current == expected;
        }
    }
}

function SumOfOddFourthPowers(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else SumOfOddFourthPowers(n - 1) + Pow4(2 * n - 1)
}

function Pow4(x: int): int
{
    x * x * x * x
}
// </vc-helpers>

// <vc-spec>
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
// </vc-spec>
// <vc-code>
{
    SumOfFourthPowerHelper(n);
    sum := n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15;
}
// </vc-code>

