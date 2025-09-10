function CountOnesInBinary(n: int): int
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 1 then 1 + CountOnesInBinary(n / 2)
    else CountOnesInBinary(n / 2)
}

predicate ValidInput(x: int) {
    x >= 1
}

predicate ValidOutput(x: int, result: int) {
    ValidInput(x) && result == CountOnesInBinary(x)
}

// <vc-helpers>
lemma CountOnesInBinaryLemma(n: int)
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n > 1 {
        if n % 2 == 1 {
            CountOnesInBinaryLemma(n / 2);
        } else {
            CountOnesInBinaryLemma(n / 2);
        }
    }
}

function CountOnes(n: int): int
    requires n >= 0
    decreases n
{
    if n == 0 then 0
    else (n % 2) + CountOnes(n / 2)
}

lemma CountOnesInBinaryLemma2(n: int)
    requires n >= 1
    ensures CountOnesInBinary(n) == CountOnes(n)
    decreases n
{
    if n > 1 {
        if n % 2 == 1 {
            CountOnesInBinaryLemma2(n / 2);
        } else {
            CountOnesInBinaryLemma2(n / 2);
        }
    }
}

lemma CountOnesProperties(n: int)
    requires n >= 0
    ensures CountOnes(n) <= n
    decreases n
{
    if n > 0 {
        CountOnesProperties(n / 2);
        // Additional knowledge about division
        assert n / 2 < n;
    }
}

lemma CountOnesMonotonic(m: int, n: int)
    requires 0 <= m <= n
    ensures CountOnes(m) <= CountOnes(n)
    decreases n
{
    if m < n {
        CountOnesMonotonic(m, n - 1);
        // Prove that CountOnes(n) >= CountOnes(n - 1)
        if n > 0 {
            var prev := n - 1;
            // Handle the case where n and n-1 might have different binary representations
            // This is a simplified version that should work for most cases
            if n % 2 == 0 {
                // When n is even, n-1 is odd and might have more ones
                CountOnesMonotonic(n - 1, n);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
    result := 0;
    var current := x;
    
    while (current > 0)
        invariant current >= 0
        invariant result + CountOnes(current) == CountOnes(x)
        decreases current
    {
        result := result + (current % 2);
        current := current / 2;
        
        if current > 0 {
            CountOnesProperties(current);
        }
    }
    
    CountOnesInBinaryLemma2(x);
}
// </vc-code>

