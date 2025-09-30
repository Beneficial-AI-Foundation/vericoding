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
/* helper modified by LLM (iteration 2): arithmetic lemmas for parity and cancellation used to prove correctness */
proof fn lemma_odd_implies_even_after_minus_three(r: int)
    requires
        r % 2 == 1,
    ensures
        (r - 3) % 2 == 0,
{
}

/* helper modified by LLM (iteration 2): if n is even, then 2 * (n/2) == n */
proof fn lemma_even_div2_mul2_cancel(n: int)
    requires
        n % 2 == 0,
    ensures
        2 * (n / 2) == n,
{
}

/* helper modified by LLM (iteration 2): show that for odd r > 4, choosing x=1 and y=(r-3)/2 yields h(1,y)=r and y>0 */
proof fn lemma_h_solution_y_pos(r: int)
    requires
        r > 4,
        r % 2 == 1,
    ensures
        h(1, ((r - 3) / 2)) == r,
        ((r - 3) / 2) > 0,
{
    lemma_odd_implies_even_after_minus_three(r);
    lemma_even_div2_mul2_cancel(r - 3);
    let y = (r - 3) / 2;
    assert(r - 3 >= 2);
    assert(y >= 1);
    assert(h(1, y) == 2 * y + 3);
    assert(2 * y == r - 3);
    assert(2 * y + 3 == r);
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
    /* code modified by LLM (iteration 2): implement conditional construction and reason in proof blocks using ints */
    if r > 4 && r % 2 == 1 {
        let y: i8 = (r - 3) / 2;
        let mut v: Vec<i8> = Vec::new();
        v.push(1i8);
        v.push(y);
        proof {
            let r_int: int = r as int;
            let y_int: int = y as int;

            // Relate machine-int computation to mathematical-int formula
            assert(y_int == (r_int - 3) / 2);

            // Use helper lemma to establish correctness and positivity
            lemma_h_solution_y_pos(r_int);
            assert(((r_int - 3) / 2) > 0);
            assert(y_int > 0);

            // Establish properties about the constructed vector
            assert(v@.len() == 2);
            assert(v@[0] == 1i8);
            assert(v@[1] == y);

            let m = v@.map(|i: int, x: i8| x as int);
            assert(m.len() == 2);
            assert(m[0] == 1);
            assert(m[1] == y_int);
            assert(m[0] > 0);
            assert(m[1] > 0);

            // Show h(result[0], result[1]) == r
            assert(h(1, ((r_int - 3) / 2)) == r_int);
            assert(h(1, y_int) == r_int);
            assert(h(m[0], m[1]) == r_int);

            // Strengthen specialized postconditions
            assert(v@[0] as int == 1);
            assert(v@[1] as int == ((r as int) - 3) / 2);
        }
        v
    } else {
        Vec::new()
    }
}
// </vc-code>


}

fn main() {}