use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::external_body]
fn add_one(n: i32) -> (result: i32)
    ensures
        result == n + 1,
{
    n + 1
}

#[verifier::external_body]
fn square(n: i32) -> (result: i32)
    ensures
        n * n == result,
{
    n * n
}

proof fn square_monotonic(a: i32, b: i32)
    requires
        0 <= a,
        a <= b,
    ensures
        a * a <= b * b,
{
    if a < b {
        assert((b - a) > 0);
        assert(b * b == a * a + 2 * a * (b - a) + (b - a) * (b - a));
        assert(a * a <= b * b);
    } else {
        assert(a == b);
        assert(a * a == b * b);
    }
}
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut low: i32 = 1;
    let mut high: i32 = n;
    let mut result: i32 = 0;

    while low <= high
        invariant
            1 <= low,
            low <= high + 1,
            high <= n,
            result * result <= n,
            0 <= result,
    {
        let mid: i32 = low + (high - low) / 2;
        let mid_squared: i32 = square(mid);

        if mid_squared <= n {
            result = mid;
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    proof {
        if result + 1 <= n {
            square_monotonic(result, result + 1);
            assert((result + 1) * (result + 1) > n);
        }
    }

    result
}
// </vc-code>

fn main() {}
}