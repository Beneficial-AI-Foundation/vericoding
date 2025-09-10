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
lemma MaxExpressionIsCorrect(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures IsMaxOfAllExpressions(MaxExpression(a, b, c), a, b, c)
{
    var exprs := AllExpressions(a, b, c);
    var max := MaxExpression(a, b, c);
    
    if max == exprs[0] {
        assert max >= exprs[1] && max >= exprs[2] && max >= exprs[3] && max >= exprs[4] && max >= exprs[5];
    } else if max == exprs[1] {
        assert max >= exprs[2] && max >= exprs[3] && max >= exprs[4] && max >= exprs[5];
        assert !(exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5]);
        assert max >= exprs[0];
    } else if max == exprs[2] {
        assert max >= exprs[3] && max >= exprs[4] && max >= exprs[5];
        assert !(exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5]);
        assert !(exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5]);
        assert max >= exprs[0] && max >= exprs[1];
    } else if max == exprs[3] {
        assert max >= exprs[4] && max >= exprs[5];
        assert !(exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5]);
        assert !(exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5]);
        assert !(exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5]);
        assert max >= exprs[0] && max >= exprs[1] && max >= exprs[2];
    } else if max == exprs[4] {
        assert max >= exprs[5];
        assert !(exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5]);
        assert !(exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5]);
        assert !(exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5]);
        assert !(exprs[3] >= exprs[4] && exprs[3] >= exprs[5]);
        assert max >= exprs[0] && max >= exprs[1] && max >= exprs[2] && max >= exprs[3];
    } else {
        assert max == exprs[5];
        assert !(exprs[0] >= exprs[1] && exprs[0] >= exprs[2] && exprs[0] >= exprs[3] && exprs[0] >= exprs[4] && exprs[0] >= exprs[5]);
        assert !(exprs[1] >= exprs[2] && exprs[1] >= exprs[3] && exprs[1] >= exprs[4] && exprs[1] >= exprs[5]);
        assert !(exprs[2] >= exprs[3] && exprs[2] >= exprs[4] && exprs[2] >= exprs[5]);
        assert !(exprs[3] >= exprs[4] && exprs[3] >= exprs[5]);
        assert !(exprs[4] >= exprs[5]);
        assert max >= exprs[0] && max >= exprs[1] && max >= exprs[2] && max >= exprs[3] && max >= exprs[4];
    }
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
    result := MaxExpression(a, b, c);
    MaxExpressionIsCorrect(a, b, c);
}
// </vc-code>

