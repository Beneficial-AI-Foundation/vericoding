use vstd::prelude::*;

verus! {

//IMPL triangle_area
fn triangle_area(a: u64, h: u64) -> (area: u64)
    // pre-conditions-start
    requires
        a > 0,
        h > 0,
        a * h / 2 <= u64::MAX
        ,
    // pre-conditions-end
    // post-conditions-start
    ensures
        area == a * h / 2,
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fix arithmetic assertions by using proper multiplication properties and removing problematic assertions */
    if a % 2 == 0 {
        let half_a = a / 2;
        assert(a == 2 * half_a);
        assert(half_a * h == (2 * half_a) * h / 2) by {
            /* code modified by LLM (iteration 1): Use multiplication commutativity and associativity correctly */
            assert((2 * half_a) * h == 2 * (half_a * h)) by {
                // This follows from associativity of multiplication
            }
            assert(2 * (half_a * h) / 2 == half_a * h) by {
                // This follows from division canceling multiplication by 2
            }
        }
        assert(half_a * h <= u64::MAX) by {
            assert(a * h / 2 <= u64::MAX);
            assert(a * h == 2 * half_a * h);
            assert(2 * half_a * h / 2 == half_a * h);
        }
        half_a * h
    } else if h % 2 == 0 {
        let half_h = h / 2;
        assert(h == 2 * half_h);
        assert(a * half_h == a * (2 * half_h) / 2) by {
            /* code modified by LLM (iteration 1): Use multiplication distributivity correctly */
            assert(a * (2 * half_h) == (a * 2) * half_h) by {
                // This follows from associativity of multiplication
            }
            assert((a * 2) * half_h == 2 * a * half_h) by {
                // This follows from commutativity of multiplication
            }
            assert(2 * a * half_h / 2 == a * half_h) by {
                // This follows from division canceling multiplication by 2
            }
        }
        assert(a * half_h <= u64::MAX) by {
            assert(a * h / 2 <= u64::MAX);
            assert(a * h == a * 2 * half_h);
            assert(a * 2 * half_h / 2 == a * half_h);
        }
        a * half_h
    } else {
        // Both a and h are odd, so a * h is odd, and a * h / 2 truncates
        // We need to compute (a * h) / 2 directly
        assert(a * h <= u64::MAX) by {
            assert(a * h / 2 <= u64::MAX);
            assert(a * h / 2 < a * h);
        }
        (a * h) / 2
    }
}

}
fn main() {}