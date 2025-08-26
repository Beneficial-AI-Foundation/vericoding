// <vc-helpers>
lemma SumOfSquaresLemma(k: int)
    requires k >= 0
    ensures k * (2 * k - 1) * (2 * k + 1) + 3 * (2 * k + 1) * (2 * k + 1) == (k + 1) * (2 * (k + 1) - 1) * (2 * (k + 1) + 1)
{
    // We need to prove: k(2k-1)(2k+1) + 3(2k+1)² = (k+1)(2k+1)(2k+3)
    
    var left := k * (2 * k - 1) * (2 * k + 1) + 3 * (2 * k + 1) * (2 * k + 1);
    var right := (k + 1) * (2 * (k + 1) - 1) * (2 * (k + 1) + 1);
    
    // Simplify the right side
    assert 2 * (k + 1) - 1 == 2 * k + 1;
    assert 2 * (k + 1) + 1 == 2 * k + 3;
    
    // Factor out (2k+1) from the left side
    calc {
        left;
    ==  k * (2 * k - 1) * (2 * k + 1) + 3 * (2 * k + 1) * (2 * k + 1);
    ==  (2 * k + 1) * (k * (2 * k - 1) + 3 * (2 * k + 1));
    ==  (2 * k + 1) * (2 * k * k - k + 3 * (2 * k + 1));
    ==  (2 * k + 1) * (2 * k * k - k + 6 * k + 3);
    ==  (2 * k + 1) * (2 * k * k + 5 * k + 3);
    }
    
    calc {
        right;
    ==  (k + 1) * (2 * k + 1) * (2 * k + 3);
    ==  (2 * k + 1) * (k + 1) * (2 * k + 3);
    ==  (2 * k + 1) * ((k + 1) * (2 * k + 3));
    ==  (2 * k + 1) * (2 * k * k + 3 * k + 2 * k + 3);
    ==  (2 * k + 1) * (2 * k * k + 5 * k + 3);
    }
}
// </vc-helpers>

// <vc-spec>
method SumOfSquaresOfFirstNOddNumbers(n: int) returns (sum: int)
    requires n >= 0
    ensures sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
// </vc-spec>
// <vc-code>
{
    sum := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant sum * 3 == i * (2 * i - 1) * (2 * i + 1)
    {
        var oddNumber := 2 * i + 1;
        sum := sum + oddNumber * oddNumber;
        i := i + 1;
        
        // Use the helper lemma to prove invariant maintenance
        SumOfSquaresLemma(i - 1);
    }
}
// </vc-code>