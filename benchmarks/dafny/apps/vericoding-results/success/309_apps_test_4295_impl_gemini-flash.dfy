predicate ValidInput(n: int, k: int) {
    n >= 0 && k >= 1
}

function MinValue(n: int, k: int): int
    requires ValidInput(n, k)
{
    var remainder := n % k;
    var complement := k - remainder;
    if remainder <= complement then remainder else complement
}

predicate IsCorrectResult(n: int, k: int, result: int) 
    requires ValidInput(n, k)
{
    result == MinValue(n, k) &&
    result >= 0 &&
    result < k
}

// <vc-helpers>
function MinValueHelper(n: int, k: int): int
    requires n >= 0 && k >= 1
    ensures 0 <= MinValueHelper(n, k) < k
    ensures MinValueHelper(n,k) == n % k || MinValueHelper(n,k) == k - (n % k)
    ensures n % k == MinValueHelper(n,k) || k - (n % k) == MinValueHelper(n,k)
{
    var remainder := n % k;
    var complement := k - remainder;
    if remainder <= complement then remainder else complement
}

predicate ValidInputHelper(n: int, k: int) {
    n >= 0 && k >= 1
}

predicate IsCorrectResultHelper(n: int, k: int, result: int) 
    requires ValidInputHelper(n, k)
{
    result == MinValueHelper(n, k) &&
    result >= 0 &&
    result < k
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
    var remainder := n % k;
    var complement := k - remainder;
    if remainder <= complement {
        result := remainder;
    } else {
        result := complement;
    }
}
// </vc-code>

