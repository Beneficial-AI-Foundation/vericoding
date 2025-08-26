function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).


lemma distributiveProperty(x: real, a: nat, b: nat)
    ensures power(x, a) * power(x, b) == power(x, a+b)
{
    if a == 0 {
        assert
            power(x, a) * power(x, b) ==
            power(x, b) ==
            power(x, a + b);
    }
    else {
        distributiveProperty(x, a-1, b);
        assert
            power(x, a) * power(x, b) ==
            (x * power(x, a-1)) * power(x, b) ==
            x * (power(x, a-1) * power(x, b)) ==
            x * power(x, a - 1 + b) ==
            power(x, a + b);
    }
}
// Recursive version, imperative, with time and space complexity O(log n).

// <vc-helpers>
lemma powerSquareProperty(x: real, n: nat)
    ensures power(x * x, n) == power(x, 2 * n)
{
    if n == 0 {
        assert power(x * x, n) == 1.0 == power(x, 2 * n);
    } else {
        powerSquareProperty(x, n-1);
        distributiveProperty(x, 2, 2 * (n-1));
        assert 2 + 2 * (n-1) == 2 * n;
        assert power(x * x, n) == (x * x) * power(x * x, n-1) == 
               (x * x) * power(x, 2 * (n-1)) ==
               power(x, 2) * power(x, 2 * (n-1)) ==
               power(x, 2 + 2 * (n-1)) ==
               power(x, 2 * n);
    }
}
// </vc-helpers>

method powerOpt(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1.0;
    }
    
    var base := b;
    var exp := n;
    var result := 1.0;
    
    while exp > 0
        invariant result * power(base, exp) == power(b, n)
        decreases exp
    {
        if exp % 2 == 1 {
            result := result * base;
            exp := exp - 1;
        } else {
            powerSquareProperty(base, exp / 2);
            base := base * base;
            exp := exp / 2;
        }
    }
    
    return result;
}
// </vc-code>

// A simple test case to make sure the specification is adequate.