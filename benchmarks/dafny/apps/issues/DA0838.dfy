// <vc-preamble>
predicate ValidInput(A: int, B: int)
{
    0 <= A <= 1000000000 && 0 <= B <= 1000000000 && A != B
}

predicate HasSolution(A: int, B: int)
{
    (A + B) % 2 == 0
}

function ComputeK(A: int, B: int): int
    requires HasSolution(A, B)
{
    (A + B) / 2
}

predicate IsValidK(A: int, B: int, K: int)
{
    abs(A - K) == abs(B - K)
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
function digitToChar(d: int): char
    requires 0 <= d <= 9
{
    match d
    case 0 => '0'
    case 1 => '1'
    case 2 => '2'
    case 3 => '3'
    case 4 => '4'
    case 5 => '5'
    case 6 => '6'
    case 7 => '7'
    case 8 => '8'
    case 9 => '9'
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then intToStringPos(n)
    else "-" + intToStringPos(-n)
}

function intToStringPos(n: int): string
    requires n > 0
{
    if n < 10 then [digitToChar(n)]
    else intToStringPos(n / 10) + [digitToChar(n % 10)]
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int) returns (result: string)
    requires ValidInput(A, B)
    ensures HasSolution(A, B) ==> result == intToString(ComputeK(A, B)) + "\n"
    ensures !HasSolution(A, B) ==> result == "IMPOSSIBLE\n"
    ensures HasSolution(A, B) ==> IsValidK(A, B, ComputeK(A, B))
// </vc-spec>
// <vc-code>
{
    if (A + B) % 2 == 0 {
        var k := (A + B) / 2;
        result := intToString(k) + "\n";
    } else {
        result := "IMPOSSIBLE\n";
    }
}
// </vc-code>
