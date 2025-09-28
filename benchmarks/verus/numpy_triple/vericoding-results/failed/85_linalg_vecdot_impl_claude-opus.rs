// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added helper lemma for sequence equality proofs */
proof fn dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len(),
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1),
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        dot_product_commutative(x1.skip(1), x2.skip(1));
    }
}

proof fn lemma_seq_skip_take(s: Seq<i32>, i: int)
    requires 0 < i <= s.len(),
    ensures s.take(i).skip(1) == s.subrange(1, i),
{
    assert(s.take(i).len() == i);
    assert(s.take(i).skip(1).len() == i - 1);
    assert forall|j: int| 0 <= j < i - 1 implies s.take(i).skip(1)[j] == s.subrange(1, i)[j] by {
        assert(s.take(i).skip(1)[j] == s.take(i)[j + 1]);
        assert(s.take(i)[j + 1] == s[j + 1]);
        assert(s.subrange(1, i)[j] == s[j + 1]);
    }
}
// </vc-helpers>

// <vc-spec>
spec fn dot_product_spec(x1: Seq<i32>, x2: Seq<i32>) -> int
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
        0
    } else {
        x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1))
    }
}

fn vecdot(x1: Vec<i32>, x2: Vec<i32>) -> (result: i32)
    requires x1.len() == x2.len(),
    ensures 
        result as int == dot_product_spec(x1@, x2@),
        result as int == dot_product_spec(x2@, x1@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    let n = x1.len();
    
    while i < n
        invariant
            i <= n,
            n == x1.len(),
            n == x2.len(),
            sum as int == dot_product_spec(x1@.take(i as int), x2@.take(i as int)),
        decreases n - i
    {
        let old_sum = sum;
        sum = sum + x1[i] * x2[i];
        
        proof {
            assert(x1@.take(i as int + 1) == x1@.take(i as int).push(x1@[i as int]));
            assert(x2@.take(i as int + 1) == x2@.take(i as int).push(x2@[i as int]));
            assert(dot_product_spec(x1@.take(i as int + 1), x2@.take(i as int + 1)) ==
                   x1@[i as int] * x2@[i as int] + dot_product_spec(x1@.take(i as int).skip(1), x2@.take(i as int).skip(1)));
            
            if i > 0 {
                lemma_seq_skip_take(x1@, i as int);
                assert(x1@.take(i as int).skip(1) == x1@.subrange(1, i as int));
                assert(x1@.take(i as int - 1) == x1@.subrange(0, i as int - 1));
                assert(x1@.subrange(1, i as int) == x1@.subrange(0, i as int - 1).push(x1@[i as int - 1]).subrange(1, i as int));
                
                lemma_seq_skip_take(x2@, i as int);
                assert(x2@.take(i as int).skip(1) == x2@.subrange(1, i as int));
                assert(x2@.take(i as int - 1) == x2@.subrange(0, i as int - 1));
                assert(x2@.subrange(1, i as int) == x2@.subrange(0, i as int - 1).push(x2@[i as int - 1]).subrange(1, i as int));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(x1@.take(n as int) == x1@);
        assert(x2@.take(n as int) == x2@);
        dot_product_commutative(x1@, x2@);
    }
    
    sum
}
// </vc-code>

}
fn main() {}