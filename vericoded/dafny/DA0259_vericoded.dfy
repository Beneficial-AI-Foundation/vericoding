predicate ValidInput(n: int, k: int) {
    n >= 1 && k >= 2
}

function ImpossibilityCondition(n: int, k: int): bool
    requires ValidInput(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

predicate ValidSolution(n: int, k: int, result: int)
    requires ValidInput(n, k)
{
    if ImpossibilityCondition(n, k) then
        result == -1
    else
        result >= 0 && result <= k &&
        exists x: int :: 
            x >= 0 && 
            x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0 && 
            (x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0) &&
            result == k - x
}

// <vc-helpers>
lemma QuadraticMonotonic(x: int, c: int)
    ensures x >= 0 && x * x - x + c <= 0 && (x + 1) * (x + 1) - (x + 1) + c > 0 ==>
            forall y :: y > x + 1 ==> y * y - y + c > 0
{
    if x >= 0 && x * x - x + c <= 0 && (x + 1) * (x + 1) - (x + 1) + c > 0 {
        forall y | y > x + 1
            ensures y * y - y + c > 0
        {
            assert y >= x + 2;
            var diff := (y * y - y + c) - ((x + 1) * (x + 1) - (x + 1) + c);
            assert diff == y * y - y - ((x + 1) * (x + 1) - (x + 1));
            
            // Expand (x + 1) * (x + 1) - (x + 1)
            assert (x + 1) * (x + 1) == x * x + 2 * x + 1;
            assert (x + 1) * (x + 1) - (x + 1) == x * x + 2 * x + 1 - x - 1;
            assert (x + 1) * (x + 1) - (x + 1) == x * x + x;
            
            // Now diff = y * y - y - (x * x + x)
            assert diff == y * y - y - x * x - x;
            assert diff == (y * y - x * x) - (y + x);
            assert y * y - x * x == (y - x) * (y + x);
            assert diff == (y - x) * (y + x) - (y + x);
            assert diff == (y + x) * (y - x - 1);
            
            // Since y >= x + 2, we have y - x - 1 >= 1
            assert y - x - 1 >= 1;
            // Since y >= x + 2 and x >= 0, we have y + x >= x + 2 + x = 2x + 2 >= 2
            assert y + x >= 2;
            assert diff >= 2 * 1;
            assert diff > 0;
        }
    }
}

lemma ValidSolutionUnique(n: int, k: int, x: int)
    requires ValidInput(n, k)
    requires !ImpossibilityCondition(n, k)
    requires x >= 0
    requires x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0
    requires x == 0 || (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
    ensures ValidSolution(n, k, k - x)
{
    var c := 2 * (n - 1) - k * (k - 1);
    assert c <= 0;
    
    if x > 0 {
        QuadraticMonotonic(x, c);
    }
    
    assert exists y: int :: 
        y >= 0 && 
        y * y - y + c <= 0 && 
        (y == 0 || (y + 1) * (y + 1) - (y + 1) + c > 0) &&
        k - x == k - y
    by {
        assert x >= 0 && x * x - x + c <= 0 && (x == 0 || (x + 1) * (x + 1) - (x + 1) + c > 0);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures result >= -1
    ensures (result == -1) <==> ImpossibilityCondition(n, k)
    ensures ValidSolution(n, k, result)
// </vc-spec>
// <vc-code>
{
    var c := 2 * (n - 1) - k * (k - 1);
    
    if c > 0 {
        result := -1;
        assert ImpossibilityCondition(n, k);
        assert ValidSolution(n, k, result);
    } else {
        var x := 0;
        
        while x <= k && x * x - x + c <= 0
            invariant 0 <= x <= k + 1
            invariant forall i :: 0 <= i < x ==> i * i - i + c <= 0
        {
            x := x + 1;
        }
        
        x := x - 1;
        
        assert x >= 0;
        assert x * x - x + c <= 0;
        assert (x + 1) * (x + 1) - (x + 1) + c > 0 || x == k;
        
        if x == k {
            assert (x + 1) * (x + 1) - (x + 1) + c == (k + 1) * (k + 1) - (k + 1) + c;
            assert (k + 1) * (k + 1) - (k + 1) + c == k * k + 2 * k + 1 - k - 1 + c;
            assert k * k + 2 * k + 1 - k - 1 + c == k * k + k + c;
            assert k * k + k + c == k * k + k + 2 * (n - 1) - k * (k - 1);
            assert k * k + k + 2 * (n - 1) - k * (k - 1) == k * k + k + 2 * (n - 1) - k * k + k;
            assert k * k + k + 2 * (n - 1) - k * k + k == 2 * k + 2 * (n - 1);
            assert 2 * k + 2 * (n - 1) == 2 * (k + n - 1);
            assert 2 * (k + n - 1) > 0;
            assert (x + 1) * (x + 1) - (x + 1) + c > 0;
        }
        
        result := k - x;
        
        assert result >= 0;
        assert result <= k;
        ValidSolutionUnique(n, k, x);
        assert ValidSolution(n, k, result);
    }
}
// </vc-code>

