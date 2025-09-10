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
function max(x: int, y: int): int {
  if x >= y then x else y
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

    var currentMax := exprs[0];
    assert exprs[0] == a * b * c;
    assert currentMax == a * b * c;
    assert forall i | 0 <= i < |exprs| ::
        i == 0 ==> currentMax >= exprs[i];

    currentMax := max(currentMax, exprs[1]);
    assert currentMax == max(a * b * c, a + b * c);
    assert forall i | 0 <= i < |exprs| ::
        i == 0 || i == 1 ==> currentMax >= exprs[i];

    currentMax := max(currentMax, exprs[2]);
    assert currentMax == max(max(a * b * c, a + b * c), a * b + c);
    assert forall i | 0 <= i < |exprs| ::
        i == 0 || i == 1 || i == 2 ==> currentMax >= exprs[i];

    currentMax := max(currentMax, exprs[3]);
    assert currentMax == max(max(max(a * b * c, a + b * c), a * b + c), a * (b + c));
    assert forall i | 0 <= i < |exprs| ::
        i == 0 || i == 1 || i == 2 || i == 3 ==> currentMax >= exprs[i];

    currentMax := max(currentMax, exprs[4]);
    assert currentMax == max(max(max(max(a * b * c, a + b * c), a * b + c), a * (b + c)), (a + b) * c);
    assert forall i | 0 <= i < |exprs| ::
        i == 0 || i == 1 || i == 2 || i == 3 || i == 4 ==> currentMax >= exprs[i];

    currentMax := max(currentMax, exprs[5]);
    assert currentMax == max(max(max(max(max(a * b * c, a + b * c), a * b + c), a * (b + c)), (a + b) * c), a + b + c);
    assert forall i | 0 <= i < |exprs| :: currentMax >= exprs[i];

    result := currentMax;
    assert IsMaxOfAllExpressions(result, a, b, c);
    assert result == MaxExpression(a, b, c);
}
// </vc-code>

