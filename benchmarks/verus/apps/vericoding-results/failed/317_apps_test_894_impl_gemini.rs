// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    x != 0 && y != 0
}

spec fn valid_output(result: Seq<int>, x: int, y: int) -> bool {
    result.len() == 4 &&
    result[0] < result[2] &&
    (x * y > 0 && x < 0 ==> result =~= seq![x + y, 0, 0, x + y]) &&
    (x * y > 0 && x >= 0 ==> result =~= seq![0, x + y, x + y, 0]) &&
    (x * y <= 0 && x < 0 ==> result =~= seq![x - y, 0, 0, y - x]) &&
    (x * y <= 0 && x >= 0 ==> result =~= seq![0, y - x, x - y, 0])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed incorrect std lib lemma name. */
proof fn lemma_sign_product(x: int, y: int)
    requires
        x != 0,
        y != 0,
    ensures
        ((x > 0 && y > 0) || (x < 0 && y < 0)) <==> (x * y > 0),
{
    vstd::arithmetic::mul::lemma_mul_basics(x, y);
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: Vec<i8>)
    requires valid_input(x as int, y as int)
    ensures valid_output(result@.map(|i: int, v: i8| v as int), x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): This code now relies on the corrected helper lemma. */
    if (x > 0) == (y > 0) { // Same sign
        proof {
            let xi = x as int;
            let yi = y as int;
            lemma_sign_product(xi, yi);
            assert(xi * yi > 0);
        }
        
        let val = (x as i16 + y as i16) as i8;
        if x > 0 { // Both positive
            proof {
                assert((x as int) >= 0);
            }
            vec![0, val, val, 0]
        } else { // Both negative
            proof {
                assert((x as int) < 0);
            }
            vec![val, 0, 0, val]
        }
    } else { // Different signs
        proof {
            let xi = x as int;
            let yi = y as int;
            lemma_sign_product(xi, yi);
            assert(xi * yi <= 0);
        }

        let val1 = (x as i16 - y as i16) as i8;
        let val2 = (y as i16 - x as i16) as i8;

        if x < 0 { // x negative, y positive
            proof {
                assert((x as int) < 0);
            }
            vec![val1, 0, 0, val2]
        } else { // x positive, y negative
            proof {
                assert((x as int) >= 0);
            }
            vec![0, val2, val1, 0]
        }
    }
}
// </vc-code>


}

fn main() {}