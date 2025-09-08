Given a hash function H(x,y) = x² + 2xy + x + 1 where x and y are positive integers,
determine if there exists a pair of positive integers (x,y) such that H(x,y) = r 
for a given positive integer r. If such a pair exists, return the pair (x,y) with 
the smallest possible value of x. If no such pair exists, return empty sequence.

function H(x: int, y: int): int
{
    x * x + 2 * x * y + x + 1
}

predicate ValidInput(r: int)
{
    r > 0
}

predicate ValidSolution(result: seq<int>, r: int)
{
    if |result| == 0 then
        true
    else
        |result| == 2 && result[0] > 0 && result[1] > 0 && H(result[0], result[1]) == r
}

predicate HasSolution(r: int)
{
    r > 4 && r % 2 == 1
}

method solve(r: int) returns (result: seq<int>)
    requires ValidInput(r)
    ensures ValidSolution(result, r)
    ensures |result| == 0 || |result| == 2
    ensures |result| == 2 ==> result[0] > 0 && result[1] > 0
    ensures |result| == 2 ==> H(result[0], result[1]) == r
    ensures r <= 4 ==> |result| == 0
    ensures r > 4 && r % 2 == 0 ==> |result| == 0
    ensures r > 4 && r % 2 == 1 ==> |result| == 2 && result[0] == 1 && result[1] == (r - 3) / 2
{
    if r <= 4 {
        result := [];
    } else if r % 2 == 0 {
        result := [];
    } else {
        var y := (r - 3) / 2;
        result := [1, y];
    }
}
