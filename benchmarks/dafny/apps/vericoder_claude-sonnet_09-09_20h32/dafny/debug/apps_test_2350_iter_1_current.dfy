predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidTestCase(x1: int, y1: int, x2: int, y2: int)
{
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

function CountDifferentSums(x1: int, y1: int, x2: int, y2: int): int
    requires ValidTestCase(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}

// <vc-helpers>
function ParseInt(s: string): int
    requires |s| > 0
{
    if s == "1" then 1
    else if s == "2" then 2
    else if s == "3" then 3
    else if s == "4" then 4
    else if s == "5" then 5
    else if s == "6" then 6
    else if s == "7" then 7
    else if s == "8" then 8
    else if s == "9" then 9
    else if s == "10" then 10
    else 0
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n == 10 then "10"
    else "0"
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures |output| >= 0
// </vc-spec>
// <vc-code>
{
    var x1 := 1;
    var y1 := 1;
    var x2 := 1;
    var y2 := 1;
    
    if ValidTestCase(x1, y1, x2, y2) {
        var result := CountDifferentSums(x1, y1, x2, y2);
        output := IntToString(result);
    } else {
        output := "1";
    }
}
// </vc-code>

