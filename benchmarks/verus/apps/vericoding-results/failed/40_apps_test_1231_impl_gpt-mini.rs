// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    0 <= a <= 100 && 0 <= b <= 100
}

spec fn valid_output(result: String) -> bool {
    result@ == "YES"@ || result@ == "NO"@
}

spec fn interval_exists(a: int, b: int) -> bool {
    abs_spec(a - b) <= 1 && a + b > 0
}

spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove nonnegativity of inputs */
proof fn lemma_nonneg(a: i8, b: i8)
    requires
        valid_input(a as int, b as int),
    ensures
        a as int >= 0,
        b as int >= 0,
{
    assert(0 <= a as int);
    assert(0 <= b as int);
}

/* helper modified by LLM (iteration 4): relate runtime differences/sum to spec predicate */
proof fn lemma_interval_equiv(a: i8, b: i8, diff_i16: i16, sum_i16: i16)
    requires
        valid_input(a as int, b as int),
        diff_i16 == if a >= b { (a - b) as i16 } else { (b - a) as i16 },
        sum_i16 == (a as i16) + (b as i16),
    ensures
        (diff_i16 <= 1 && sum_i16 > 0) <==> interval_exists(a as int, b as int),
{
    let ai = a as int;
    let bi = b as int;
    // relate the runtime difference to the mathematical absolute difference
    assert((if a >= b { (a - b) as int } else { (b - a) as int }) == diff_i16 as int);
    assert((if a >= b { (a - b) as int } else { (b - a) as int }) == if ai >= bi { ai - bi } else { bi - ai });
    assert(abs_spec(ai - bi) == if ai >= bi { ai - bi } else { bi - ai });
    assert(diff_i16 as int == abs_spec(ai - bi));
    // relate the runtime sum to the spec sum
    assert(sum_i16 as int == ai + bi);
    // establish equivalence between runtime condition and spec predicate
    assert((diff_i16 <= 1 && sum_i16 > 0) <==> (abs_spec(ai - bi) <= 1 && ai + bi > 0));
    assert((diff_i16 <= 1 && sum_i16 > 0) <==> interval_exists(ai, bi));
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int)
    ensures 
        valid_output(result) &&
        ((result@ == "YES"@) <==> interval_exists(a as int, b as int))
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): compute runtime values and apply lemma to prove spec equivalence */
    let diff_i16 = if a >= b { (a - b) as i16 } else { (b - a) as i16 };
    let sum_i16 = (a as i16) + (b as i16);
    proof {
        lemma_interval_equiv(a, b, diff_i16, sum_i16);
    }
    if diff_i16 <= 1 && sum_i16 > 0 {
        let result = String::from_str("YES");
        proof {
            // from the lemma we get the spec predicate, and we record the returned string
            lemma_interval_equiv(a, b, diff_i16, sum_i16);
            assert(result@ == "YES"@);
            let ai = a as int;
            let bi = b as int;
            assert(interval_exists(ai, bi));
        }
        result
    } else {
        let result = String::from_str("NO");
        proof {
            lemma_interval_equiv(a, b, diff_i16, sum_i16);
            assert(result@ == "NO"@);
            let ai = a as int;
            let bi = b as int;
            assert(!interval_exists(ai, bi));
        }
        result
    }
}

// </vc-code>


}

fn main() {}