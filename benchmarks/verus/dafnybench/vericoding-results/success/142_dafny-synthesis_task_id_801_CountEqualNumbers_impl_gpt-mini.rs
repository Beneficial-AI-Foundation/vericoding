use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
fn count_equal_numbers(a: i32, b: i32, c: i32) -> (count: i32)
    ensures 
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c),
// </vc-spec>
// <vc-code>
{
    let ab = a == b;
    let bc = b == c;
    let ac = a == c;

    if ab && bc {
        let count: i32 = 3;
        proof {
            // range
            assert(count >= 0 && count <= 3);

            // count == 3 <==> all equal
            assert((count == 3) <==> (ab && bc));

            // count == 2 <==> exactly one pair equal (all such disjuncts are false here)
            assert((count == 2) <==> ((ab && !bc) || (!ab && bc) || (ac && !bc)));

            // count == 1 <==> all distinct (false here)
            assert((count == 1) <==> (!ab && !bc && !ac));
        }
        count
    } else if ab && !bc {
        let count: i32 = 2;
        proof {
            // range
            assert(count >= 0 && count <= 3);

            // all equal is false here
            assert((count == 3) <==> (ab && bc));

            // count == 2 <==> one of the three "exactly-two" patterns
            // Left holds (we are in this branch), so the equivalence is true
            assert((count == 2) <==> ((ab && !bc) || (!ab && bc) || (ac && !bc)));

            // count == 1 false here
            assert((count == 1) <==> (!ab && !bc && !ac));
        }
        count
    } else if !ab && bc {
        let count: i32 = 2;
        proof {
            assert(count >= 0 && count <= 3);

            assert((count == 3) <==> (ab && bc));

            assert((count == 2) <==> ((ab && !bc) || (!ab && bc) || (ac && !bc)));

            assert((count == 1) <==> (!ab && !bc && !ac));
        }
        count
    } else if ac && !bc {
        let count: i32 = 2;
        proof {
            assert(count >= 0 && count <= 3);

            assert((count == 3) <==> (ab && bc));

            assert((count == 2) <==> ((ab && !bc) || (!ab && bc) || (ac && !bc)));

            assert((count == 1) <==> (!ab && !bc && !ac));
        }
        count
    } else {
        let count: i32 = 1;
        proof {
            assert(count >= 0 && count <= 3);

            assert((count == 3) <==> (ab && bc));

            assert((count == 2) <==> ((ab && !bc) || (!ab && bc) || (ac && !bc)));

            assert((count == 1) <==> (!ab && !bc && !ac));
        }
        count
    }
}
// </vc-code>

fn main() {}

}