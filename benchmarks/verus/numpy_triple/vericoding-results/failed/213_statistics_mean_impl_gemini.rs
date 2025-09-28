// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No material changes to helpers. */
fn compute_sum_i64(a: &Vec<i32>) -> (sum: i64)
    ensures sum as int == vec_sum(a@),
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == vec_sum(a@.subrange(0, i as int)),
        decreases a.len() - i
    {
        sum = sum + a[i] as i64;
        i = i + 1;
    }
    sum
}

proof fn lemma_all_equal_sum(a: Seq<i32>)
    requires
        a.len() > 0,
        all_equal(a),
    ensures
        vec_sum(a) == (a[0] as int) * (a.len() as int),
    decreases a.len()
{
    if a.len() > 1 {
        reveal(all_equal);
        lemma_all_equal_sum(a.skip(1));
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] as int + vec_sum(a.skip(1))
    }
}

spec fn all_equal(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

fn mean(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures 
        /* Core property: mean * count == sum */
        (result as int) * (a.len() as int) == vec_sum(a@),
        /* For constant vectors, mean equals the constant */
        all_equal(a@) ==> result == a[0]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by correcting lemma arguments. */
    let sum = compute_sum_i64(&a);
    let len = a.len() as i64;
    let result = (sum / len) as i32;

    proof {
        vstd::arithmetic::div_mod::lemma_div_mod(sum as int, len as int);
        if all_equal(a@) {
            lemma_all_equal_sum(a@);
            vstd::arithmetic::div_mod::lemma_mod_of_multiple(a@[0] as int, len as int);
            vstd::arithmetic::div_mod::lemma_div_by_multiple(a@[0] as int, len as int);
        }
    }

    result
}
// </vc-code>


}
fn main() {}