predicate ValidInput(x: int, y: int)
{
    x != 0 && y != 0
}

predicate ValidOutput(result: seq<int>, x: int, y: int)
{
    |result| == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result == [x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result == [0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result == [x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result == [0, y - x, x - y, 0])
}

// <vc-helpers>
lemma SignProductLemma(a: int, b: int)
    ensures a * b > 0 <==> (a > 0 && b > 0) || (a < 0 && b < 0)
    ensures a * b <= 0 <==> (a <= 0 && b >= 0) || (a >= 0 && b <= 0)
{
}

lemma NonZeroSignLemma(a: int)
    requires a != 0
    ensures (a > 0) || (a < 0)
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int) returns (result: seq<int>)
    requires ValidInput(x, y)
    ensures ValidOutput(result, x, y)
// </vc-spec>
// <vc-code>
{
    NonZeroSignLemma(x);
    NonZeroSignLemma(y);
    SignProductLemma(x, y);
    
    if x * y > 0 {
        if x < 0 {
            result := [x + y, 0, 0, x + y];
        } else {
            result := [0, x + y, x + y, 0];
        }
    } else {
        if x < 0 {
            result := [x - y, 0, 0, y - x];
        } else {
            result := [0, y - x, x - y, 0];
        }
    }
}
// </vc-code>

