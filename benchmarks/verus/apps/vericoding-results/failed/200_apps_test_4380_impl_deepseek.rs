// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3
}

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

spec fn exists_odd_product(a: int, b: int) -> bool {
    valid_input(a, b) ==> exists|c: int| 1 <= c <= 3 && #[trigger] is_odd(a * b * c)
}

spec fn should_answer_yes(a: int, b: int) -> bool {
    valid_input(a, b) ==> (a != 2 && b != 2)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_exists_odd_product_always()
    ensures
        forall|a: int, b: int|
            valid_input(a, b) ==> exists_odd_product(a, b),
{
    assert forall|a: int, b: int|
        valid_input(a, b) implies exists_odd_product(a, b) by {
        proof {
            let a_val = a;
            let b_val = b;
            let c = if (a_val * b_val) % 2 == 0 { 1 } else { 2 };
            assert(1 <= c <= 3);
            assert(is_odd(a_val * b_val * c));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation error by removing invalid condition syntax */
    let a_int = a as int;
    let b_int = b as int;
    
    if a_int != 2 && b_int != 2 {
        let mut seq = Seq::empty();
        seq = seq.push('Y');
        seq = seq.push('e');
        seq = seq.push('s');
        seq
    } else {
        let mut seq = Seq::empty();
        seq = seq.push('N');
        seq = seq.push('o');
        seq
    }
}
// </vc-code>


}

fn main() {}