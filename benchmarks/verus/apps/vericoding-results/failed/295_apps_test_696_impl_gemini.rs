// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>
fn is_coprime(i: int, phi: int) -> (result: bool)
    requires
        i > 0,
        phi > 0,
    ensures
        result == (forall|j: int| 2 <= j <= i ==> !((phi % j == 0) && (i % j == 0))),
{
    let mut j: int = 2;
    while j <= i
        invariant
            i > 0,
            phi > 0,
            2 <= j <= i + 1,
            forall|k: int| 2 <= k < j ==> !((phi % k == 0) && (i % k == 0)),
        decreases i - j
    {
        if (phi % j == 0) && (i % j == 0) {
            return false;
        }
        j = j + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
{
    let p_int = p as int;
    if p_int == 2 {
        return 1;
    }

    let phi = p_int - 1;
    let mut count: i8 = 0;
    let mut i: i8 = 1;

    let limit = p - 1;
    while i < limit
        invariant
            p_int == p as int,
            valid_input(p_int),
            p_int > 2,
            phi == p_int - 1,
            limit == p - 1,
            1 <= i <= limit,
            count as int == Set::new(|k: int|
                1 <= k < i as int &&
                (forall|j: int| 2 <= j <= k ==> !((phi % j == 0) && (k % j == 0)))
            ).len() as int,
        decreases (limit as int) - (i as int)
    {
        let i_int = i as int;
        if is_coprime(i_int, phi) {
            count = count + 1;
        }
        i = i + 1;
    }

    return count;
}
// </vc-code>


}

fn main() {}