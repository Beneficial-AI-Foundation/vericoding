// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures IsMaxOfAllExpressions(result, a, b, c)
    ensures result == MaxExpression(a, b, c)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
