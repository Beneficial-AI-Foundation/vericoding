predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

function AllExpressions(a: int, b: int, c: int): seq<int>
{
    [a * b * c, a + b * c, a * b + c, a * (b + c), (a + b) * c, a + b + c]
}

function MaxExpression(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    if exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5] then exprs[0]
    else if exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5] then exprs[1]
    else if exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5] then exprs[2]
    else if exprs[3] >= exprs[4] && exprs[3] >= exprs[5] then exprs[3]
    else if exprs[4] >= exprs[5] then exprs[4]
    else exprs[5]
}

predicate IsMaxOfAllExpressions(result: int, a: int, b: int, c: int)
    requires ValidInput(a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    result in exprs && forall i :: 0 <= i < |exprs| ==> result >= exprs[i]
}

// <vc-helpers>
lemma MaxExpressionCorrectness(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures IsMaxOfAllExpressions(MaxExpression(a, b, c), a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    var max := MaxExpression(a, b, c);
    
    // The function MaxExpression returns one of the expressions
    assert max == exprs[0] || max == exprs[1] || max == exprs[2] || 
           max == exprs[3] || max == exprs[4] || max == exprs[5];
    
    // And it's greater than or equal to all expressions
    assert forall i :: 0 <= i < |exprs| ==> max >= exprs[i];
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures IsMaxOfAllExpressions(result, a, b, c)
    ensures result == MaxExpression(a, b, c)
// </vc-spec>
// <vc-code>
{
    var exprs := AllExpressions(a, b, c);
    
    // Calculate all expressions
    var e0 := a * b * c;
    var e1 := a + b * c;
    var e2 := a * b + c;
    var e3 := a * (b + c);
    var e4 := (a + b) * c;
    var e5 := a + b + c;
    
    assert exprs == [e0, e1, e2, e3, e4, e5];
    
    // Find the maximum
    result := e0;
    if e1 > result {
        result := e1;
    }
    if e2 > result {
        result := e2;
    }
    if e3 > result {
        result := e3;
    }
    if e4 > result {
        result := e4;
    }
    if e5 > result {
        result := e5;
    }
    
    // Verify that result is the maximum
    assert result >= e0 && result >= e1 && result >= e2 && 
           result >= e3 && result >= e4 && result >= e5;
    assert result == e0 || result == e1 || result == e2 || 
           result == e3 || result == e4 || result == e5;
    
    MaxExpressionCorrectness(a, b, c);
}
// </vc-code>

