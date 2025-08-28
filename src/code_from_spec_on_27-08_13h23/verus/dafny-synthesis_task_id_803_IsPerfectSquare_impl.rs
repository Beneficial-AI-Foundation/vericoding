use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_positive(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        a * b > 0,
{
}

proof fn lemma_mul_increases(a: int, b: int)
    requires
        a > 0,
        b > 1,
    ensures
        a * b > a,
{
}

proof fn lemma_square_lower_bound(n: int, a: int)
    requires
        a > 0,
        a * a > n,
    ensures
        forall|b: int| 0 <= b < a ==> b * b <= n,
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_perfect_square(n: int) -> (result: bool)
    requires 
        n >= 0,
    ensures 
        result == true ==> (exists|i: int| 0 <= i <= n && #[trigger] (i * i) == n),
        result == false ==> (forall|a: int| 0 < a*a < n ==> #[trigger] (a*a) != n),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn is_perfect_square(n: int) -> (result: bool)
    requires
        n >= 0,
    ensures
        result ==> (exists|i: int| 0 <= i <= n && #[trigger] (i * i) == n),
        !result ==> (forall|a: int| 0 < a * a < n ==> #[trigger] (a * a) != n),
{
    if n == 0 {
        return true;
    }

    let mut low: int = 1;
    let mut high: int = n;

    while low <= high
        invariant
            low <= high + 1,
            low >= 1,
            high <= n,
            forall|a: int| 0 < a < low ==> a * a < n,
            forall|a: int| a > high ==> a * a > n,
    {
        let mid = low + (high - low) / 2;
        let square = mid * mid;

        if square == n {
            return true;
        } else if square < n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    false
}
// </vc-code>

fn main() {}

}