predicate ValidInput(x: int, a: int, b: int)
{
    1 <= x <= 1000 &&
    1 <= a <= 1000 &&
    1 <= b <= 1000 &&
    x != a && x != b && a != b &&
    Distance(x, a) != Distance(x, b)
}

function Distance(s: int, t: int): nat
{
    if s >= t then s - t else t - s
}

predicate CorrectResult(x: int, a: int, b: int, result: string)
{
    (result == "A" <==> Distance(x, a) < Distance(x, b)) &&
    (result == "B" <==> Distance(x, b) < Distance(x, a))
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(x: int, a: int, b: int) returns (result: string)
requires ValidInput(x, a, b)
ensures result == "A" || result == "B"
ensures CorrectResult(x, a, b, result)
// </vc-spec>
// <vc-code>
{
    var distA := Distance(x, a);
    var distB := Distance(x, b);
    
    if distA < distB {
        result := "A";
    } else {
        result := "B";
    }
}
// </vc-code>

