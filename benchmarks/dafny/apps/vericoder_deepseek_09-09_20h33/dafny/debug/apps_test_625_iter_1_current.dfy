function AlternatingSum(n: int): int
    requires n > 0
{
    if n == 1 then -1
    else AlternatingSum(n-1) + (if n % 2 == 0 then n else -n)
}

predicate ValidInput(n: int) {
    n > 0
}

// <vc-helpers>
lemma AlternatingSumFormula(n: int)
    requires n > 0
    ensures AlternatingSum(n) == (if n % 2 == 0 then n / 2 else n / 2 - n)
    decreases n
{
    if n == 1 {
        // Base case: AlternatingSum(1) = -1 = 1/2 - 1 = 0 - 1
    } else {
        AlternatingSumFormula(n-1);
        
        if n % 2 == 0 {
            // When n is even: result = AlternatingSum(n-1) + n
            // AlternatingSum(n-1) = (n-1)/2 - (n-1) since n-1 is odd
            assert AlternatingSum(n) == AlternatingSum(n-1) + n;
            assert AlternatingSum(n-1) == (n-1)/2 - (n-1);
            calc {
                AlternatingSum(n);
                == 
                (n-1)/2 - (n-1) + n;
                ==
                (n-1)/2 - (n-1) + n;
                ==
                (n-1)/2 + 1;
                ==
                n/2; // Only works when n is even
            }
        } else {
            // When n is odd: result = AlternatingSum(n-1) - n
            // AlternatingSum(n-1) = (n-1)/2 since n-1 is even
            assert AlternatingSum(n) == AlternatingSum(n-1) - n;
            assert AlternatingSum(n-1) == (n-1)/2;
            calc {
                AlternatingSum(n);
                == 
                (n-1)/2 - n;
                ==
                n/2 - n; // Since n is odd, (n-1)/2 = n/2 (integer division)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == AlternatingSum(n)
    ensures n % 2 == 0 ==> result == n / 2
    ensures n % 2 != 0 ==> result == n / 2 - n
// </vc-spec>
// <vc-code>
{
    AlternatingSumFormula(n);
    if n % 2 == 0 {
        result := n / 2;
    } else {
        result := n / 2 - n;
    }
}
// </vc-code>

