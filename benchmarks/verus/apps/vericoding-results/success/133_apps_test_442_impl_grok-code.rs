// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn h(x: int, y: int) -> int {
    x * x + 2 * x * y + x + 1
}

spec fn valid_input(r: int) -> bool {
    r > 0
}

spec fn valid_solution(result: Seq<int>, r: int) -> bool {
    if result.len() == 0 {
        true
    } else {
        result.len() == 2 && result[0] > 0 && result[1] > 0 && h(result[0], result[1]) == r
    }
}

spec fn has_solution(r: int) -> bool {
    r > 4 && r % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_h_for_odd_r_greater_than_4(r: int)
    requires
        r > 4,
        r % 2 == 1,
    ensures
        h(1, (r - 3) / 2) == r,
{
    let y = (r - 3) / 2;
    assert(r % 2 == 1);
    assert((r - 3) % 2 == 0);
    assert(h(1, y) == 1 + 2 * y + 1 + 1);
    assert(y == ((r - 3) / 2));
    assert(2 * y == r - 3);
    assert(1 + 2 * y + 1 + 1 == r);
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8) -> (result: Vec<i8>)
    requires 
        valid_input(r as int)
    ensures 
        valid_solution(result@.map(|i: int, x: i8| x as int), r as int),
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 2 ==> result@[0] as int > 0 && result@[1] as int > 0,
        result@.len() == 2 ==> h(result@[0] as int, result@[1] as int) == r as int,
        r as int <= 4 ==> result@.len() == 0,
        r as int > 4 && (r as int) % 2 == 0 ==> result@.len() == 0,
        r as int > 4 && (r as int) % 2 == 1 ==> result@.len() == 2 && result@[0] as int == 1 && result@[1] as int == ((r as int) - 3) / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added proof block to call lemma for postcondition */
    if r > 4 && r % 2 == 1 {
        let y = (r - 3) / 2;
        let mut result = Vec::new();
        result.push(1);
        result.push(y);
        proof {
            lemma_h_for_odd_r_greater_than_4(r as int);
        }
        result
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}