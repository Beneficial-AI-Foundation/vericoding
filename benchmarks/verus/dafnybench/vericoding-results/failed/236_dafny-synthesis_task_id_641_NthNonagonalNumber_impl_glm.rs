use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_nonagonal_even(n: int)
    requires n >= 0
    ensures (n * (7 * n - 5)) % 2 == 0
{
    if n % 2 == 0 {
        let k = n / 2;
        assert(n == 2 * k);
        let expr = n * (7 * n - 5);
        assert(expr == 2 * k * (7 * (2 * k) - 5));
        assert(expr == 2 * (k * (14 * k - 5)));
        assert(expr % 2 == 0);
    } else {
        let k = (n - 1) / 2;
        assert(n == 2 * k + 1);
        let expr = n * (7 * n - 5);
        assert(7 * n - 5 == 7 * (2 * k + 1) - 5);
        assert(7 * n - 5 == 14 * k + 2);
        assert(7 * n - 5 == 2 * (7 * k + 1));
        assert(expr == n * 2 * (7 * k + 1));
        assert(expr == 2 * (n * (7 * k + 1)));
        assert(expr % 2 == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    let num = n * ((7 as int) * n - (5 as int));
    lemma_nonagonal_even(n);
    num / (2 as int)
}
// </vc-code>

fn main() {}

}