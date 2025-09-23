// <vc-preamble>
predicate ValidInput(x: int, y: int, n: int)
{
    -1000000000 <= x <= 1000000000 &&
    -1000000000 <= y <= 1000000000 &&
    1 <= n <= 2000000000
}

function SequenceValue(x: int, y: int, n: int): int
    requires ValidInput(x, y, n)
{
    var pattern := [x, y, y - x, -x, -y, x - y];
    pattern[(n - 1) % 6]
}

function NormalizeModulo(value: int): int
{
    var mod_result := value % 1000000007;
    if mod_result < 0 then mod_result + 1000000007 else mod_result
}

function ExpectedResult(x: int, y: int, n: int): int
    requires ValidInput(x, y, n)
{
    NormalizeModulo(SequenceValue(x, y, n))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(x: int, y: int, n: int) returns (result: int)
    requires ValidInput(x, y, n)
    ensures 0 <= result < 1000000007
    ensures result == ExpectedResult(x, y, n)
// </vc-spec>
// <vc-code>
{
    var pattern := [x, y, y - x, -x, -y, x - y];
    var index := (n - 1) % 6;
    var value := pattern[index];
    result := value % 1000000007;
    if result < 0 {
        result := result + 1000000007;
    }
}
// </vc-code>
