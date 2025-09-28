// <vc-preamble>
predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The sum function is correctly implemented for the given constraints. */
function sum(lo: int, hi: int): int
    requires lo <= hi + 1
{
    ((hi - lo + 1) * (lo + hi)) / 2
}
// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The implementation now correctly uses the sum helper function and addresses both cases for 'r'. It also removes the erroneous use of `return` in a method that isn't expected to `return` a value directly, assuming it's a method that updates `result`. */
    var k: int;
    if r < n - 1 {
        k := r;
        result := sum(1, k);
    } else {
        k := n - 1;
        result := sum(1, k);
        if r >= n {
            result := result + 1;
        }
    }
}
// </vc-code>
