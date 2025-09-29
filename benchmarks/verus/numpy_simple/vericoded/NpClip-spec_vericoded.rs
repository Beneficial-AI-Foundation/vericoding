// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix spec indexing to use int index on RHS to avoid usize/int mismatch */
proof fn index_i8_eq(a: &Vec<i8>, i: usize)
    requires
        i < a.len(),
    ensures
        a@[i as int] == a[i as int] as int,
{
}

// </vc-helpers>

// <vc-spec>
fn clip(a: Vec<i8>, min: i8, max: i8) -> (result: Vec<i8>)
    requires min < max,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> {
            if a@[i] < min as int {
                result@[i] == min as int
            } else if a@[i] > max as int {
                result@[i] == max as int
            } else {
                result@[i] == a@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement clipping loop with invariants and use helper to relate view and indexing */
    let len = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len == a.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                if a@[j] < min as int {
                    result@[j] == min as int
                } else if a@[j] > max as int {
                    result@[j] == max as int
                } else {
                    result@[j] == a@[j]
                }
            },
        decreases len - i
    {
        let x = a[i];
        proof { index_i8_eq(&a, i); }
        if x < min {
            proof {
                assert((x as int) < (min as int));
                assert(a@[i as int] == x as int);
            }
            result.push(min);
        } else if x > max {
            proof {
                assert((x as int) > (max as int));
                assert(a@[i as int] == x as int);
            }
            result.push(max);
        } else {
            proof {
                assert((min as int) <= (x as int));
                assert((x as int) <= (max as int));
                assert(a@[i as int] == x as int);
            }
            result.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}