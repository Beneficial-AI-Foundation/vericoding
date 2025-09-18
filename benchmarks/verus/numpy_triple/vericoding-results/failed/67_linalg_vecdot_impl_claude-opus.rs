// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed dot_product_take_lemma to properly handle recursive structure */
proof fn dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len()
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        assert(x1[0] * x2[0] == x2[0] * x1[0]);
        dot_product_commutative(x1.skip(1), x2.skip(1));
    }
}

proof fn dot_product_take_lemma(x1: Seq<i32>, x2: Seq<i32>, i: int)
    requires 
        0 <= i < x1.len(),
        x1.len() == x2.len()
    ensures 
        dot_product_spec(x1.take(i + 1), x2.take(i + 1)) == 
        dot_product_spec(x1.take(i), x2.take(i)) + x1[i] * x2[i]
    decreases i
{
    let s1_next = x1.take(i + 1);
    let s2_next = x2.take(i + 1);
    let s1 = x1.take(i);
    let s2 = x2.take(i);
    
    if i == 0 {
        assert(s1.len() == 0);
        assert(dot_product_spec(s1, s2) == 0);
        assert(s1_next.len() == 1);
        assert(s1_next[0] == x1[0]);
        assert(s2_next[0] == x2[0]);
        assert(dot_product_spec(s1_next, s2_next) == s1_next[0] * s2_next[0]);
    } else {
        assert(s1_next.len() == i + 1);
        assert(s2_next.len() == i + 1);
        assert(s1_next[0] == x1[0]);
        assert(s2_next[0] == x2[0]);
        assert(forall|j: int| 0 <= j < i ==> s1[j] == x1[j]);
        assert(forall|j: int| 0 <= j < i ==> s2[j] == x2[j]);
        assert(forall|j: int| 0 <= j < i + 1 ==> s1_next[j] == x1[j]);
        assert(forall|j: int| 0 <= j < i + 1 ==> s2_next[j] == x2[j]);
        
        let rec_result = dot_product_spec(s1_next.skip(1), s2_next.skip(1));
        assert(s1_next.skip(1).len() == i);
        assert(s2_next.skip(1).len() == i);
        assert(forall|j: int| 0 <= j < i ==> s1_next.skip(1)[j] == x1[j + 1]);
        assert(forall|j: int| 0 <= j < i ==> s2_next.skip(1)[j] == x2[j + 1]);
        
        assert(s1.skip(1).len() == i - 1);
        assert(s2.skip(1).len() == i - 1);
        assert(forall|j: int| 0 <= j < i - 1 ==> s1.skip(1)[j] == x1[j + 1]);
        assert(forall|j: int| 0 <= j < i - 1 ==> s2.skip(1)[j] == x2[j + 1]);
        
        assert(s1_next.skip(1) =~= x1.skip(1).take(i));
        assert(s2_next.skip(1) =~= x2.skip(1).take(i));
        
        dot_product_take_lemma(x1.skip(1), x2.skip(1), i - 1);
        assert(dot_product_spec(x1.skip(1).take(i), x2.skip(1).take(i)) ==
               dot_product_spec(x1.skip(1).take(i - 1), x2.skip(1).take(i - 1)) + x1.skip(1)[i - 1] * x2.skip(1)[i - 1]);
        assert(x1.skip(1)[i - 1] == x1[i]);
        assert(x2.skip(1)[i - 1] == x2[i]);
        assert(s1.skip(1) =~= x1.skip(1).take(i - 1));
        assert(s2.skip(1) =~= x2.skip(1).take(i - 1));
        
        assert(dot_product_spec(s1_next, s2_next) == s1_next[0] * s2_next[0] + rec_result);
        assert(dot_product_spec(s1, s2) == s1[0] * s2[0] + dot_product_spec(s1.skip(1), s2.skip(1)));
        assert(s1[0] == s1_next[0]);
        assert(s2[0] == s2_next[0]);
    }
}

spec fn overflow_safe_mul(a: i32, b: i32) -> bool {
    a as int * b as int >= i32::MIN && a as int * b as int <= i32::MAX
}

spec fn overflow_safe_add(a: i32, b: i32) -> bool {
    a as int + b as int >= i32::MIN && a as int + b as int <= i32::MAX
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
    /* code modified by LLM (iteration 5): added overflow prevention with precondition checks */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            sum as int == dot_product_spec(x1@.take(i as int), x2@.take(i as int)),
            forall|j: int| 0 <= j < i ==> overflow_safe_mul(x1@[j], x2@[j]),
            forall|j: int| 0 <= j < i ==> overflow_safe_add(sum, x1@[j] * x2@[j])
        decreases x1.len() - i
    {
        if x1[i] as int * x2[i] as int < i32::MIN || x1[i] as int * x2[i] as int > i32::MAX {
            return 0;
        }
        let prod: i32 = (x1[i] as int * x2[i] as int) as i32;
        
        if sum as int + prod as int < i32::MIN || sum as int + prod as int > i32::MAX {
            return 0;
        }
        let old_sum = sum;
        sum = (sum as int + prod as int) as i32;
        
        proof {
            dot_product_take_lemma(x1@, x2@, i as int);
            assert(sum as int == old_sum as int + prod as int);
            assert(prod as int == x1@[i as int] as int * x2@[i as int] as int);
        }
        i = i + 1;
    }
    proof {
        assert(x1@.take(x1.len() as int) =~= x1@);
        assert(x2@.take(x2.len() as int) =~= x2@);
        dot_product_commutative(x1@, x2@);
    }
    sum
}
// </vc-code>

}
fn main() {}