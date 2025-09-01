use vstd::prelude::*;

verus! {

// <vc-helpers>
fn find_sqrt_i64(i: i64, n: i64) -> i64
    requires
        0 <= i,
        i <= n,
    ensures
        (result * result) <= n,
        n < (result + 1) * (result + 1),
    decreases n - i
{
    if (i + 1) * (i + 1) <= n {
        let ip1: i64 = i + 1;
        proof {
            // from (i+1)^2 <= n and i+1 >= 0 we get i+1 <= n
            assert(0 <= ip1);
            assert(ip1 * ip1 <= n);
            // For integer ip1 >= 0, ip1*ip1 >= ip1, so ip1 <= ip1*ip1 <= n, hence ip1 <= n
            assert(ip1 * ip1 >= ip1);
            assert(ip1 <= n);
        }
        find_sqrt_i64(ip1, n)
    } else {
        i
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
    // impl-start
    let n64: i64 = n as i64;
    let res64: i64 = find_sqrt_i64(0, n64);
    let res: i32 = res64 as i32;
    proof {
        // prove the postconditions in terms of i32 as required by the spec
        assert((res64 * res64) <= n64);
        assert(n64 < (res64 + 1) * (res64 + 1));
        // cast equalities between i64 and i32 arithmetic
        assert((res64 * res64) as int == (res as int) * (res as int));
        assert(n64 as int == n as int);
        assert(((res64 + 1) * (res64 + 1)) as int == ((res + 1) as int) * ((res + 1) as int));
        // now the spec-level guarantees follow
        assert((res as int) * (res as int) <= (n as int));
        assert((n as int) < ((res + 1) as int) * ((res + 1) as int));
        // also ensure non-negativity of result*result
        assert(0 <= (res as int) * (res as int));
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}