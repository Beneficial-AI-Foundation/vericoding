// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_all_equal_implies_same(a: Seq<i32>)
    requires all_equal(a) && a.len() > 0,
    ensures forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == a[0]
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == a[0] by {
        assert(all_equal(a));
    };
}

proof fn lemma_vec_sum_same_value(a: Seq<i32>, constant: int)
    requires a.len() > 0,
    requires forall|i: int| 0 <= i < a.len() implies a[i] == constant,
    ensures vec_sum(a) == constant * a.len() as int
    decreases a.len()
{
    if a.len() > 1 {
        lemma_vec_sum_same_value(a.skip(1), constant);
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
    /* code modified by LLM (iteration 5): Fixed integer division and added proper verification */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    let len = a.len() as i32;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            sum as int == vec_sum(a@.subrange(0, i as int)),
            len > 0
        decreases a.len() - i
    {
        sum = sum + a[i];
        i = i + 1;
    }
    
    proof {
        if all_equal(a@) {
            lemma_all_equal_implies_same(a@);
            lemma_vec_sum_same_value(a@, a[0] as int);
        }
    }
    
    sum / len
}
// </vc-code>


}
fn main() {}