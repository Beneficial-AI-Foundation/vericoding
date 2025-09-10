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
function max(a: int, b: int): int
{
    if a >= b then a else b
}

lemma MaxProperties(a: int, b: int, c: int)
    ensures max(max(a, b), c) >= a
    ensures max(max(a, b), c) >= b
    ensures max(max(a, b), c) >= c
    ensures max(max(a, b), c) == a || max(max(a, b), c) == b || max(max(a, b), c) == c
{
}

lemma TriangleInequalityRelation(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures IsTriangle(a, b, c) <==> (
        var max_val := max(max(a, b), c);
        var sum_of_other_two := a + b + c - max_val;
        max_val < sum_of_other_two
    )
{
    var max_val := max(max(a, b), c);
    var sum_of_other_two := a + b + c - max_val;
    
    MaxProperties(a, b, c);
    
    if max_val == a {
        assert sum_of_other_two == b + c;
    } else if max_val == b {
        assert sum_of_other_two == a + c;
    } else {
        assert max_val == c;
        assert sum_of_other_two == a + b;
    }
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
    var max_val := if a >= b then (if a >= c then a else c) else (if b >= c then b else c);
    var sum_of_other_two := a + b + c - max_val;
    
    if max_val < sum_of_other_two {
        TriangleInequalityRelation(a, b, c);
        assert IsTriangle(a, b, c);
        result := 0;
    } else {
        TriangleInequalityRelation(a, b, c);
        assert !IsTriangle(a, b, c);
        result := max_val - sum_of_other_two + 1;
    }
    
    assert result == max(0, max_val - sum_of_other_two + 1);
    assert result == MinOperationsNeeded(a, b, c);
}
// </vc-code>

