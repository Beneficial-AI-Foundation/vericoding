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
lemma MaxLemma(x: int, y: int, z: int)
    requires 1 <= x <= 100 && 1 <= y <= 100 && 1 <= z <= 100
    ensures max(max(x, y), z) == max(x, max(y, z))
{
}

lemma SumMinusMaxIsSumOfOtherTwo(a: int, b: int, c: int)
    requires 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
    ensures a + b + c - max(max(a, b), c) == a + b + c - max(a, max(b, c))
{
    MaxLemma(a, b, c);
}

lemma MaxValSumRelation(a: int, b: int, c: int)
    requires ValidInput(a, b, c)
    ensures max_val >= sum_of_other_two ==> max_val - sum_of_other_two + 1 >= 0
    where {
        var max_val := max(max(a, b), c);
        var sum_of_other_two := a + b + c - max_val;
    }
{
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
    var max_val := max(max(a, b), c);
    var sum_of_other_two := a + b + c - max_val;
    
    if max_val < sum_of_other_two {
        result := 0;
    } else {
        result := max_val - sum_of_other_two + 1;
    }
}
// </vc-code>

