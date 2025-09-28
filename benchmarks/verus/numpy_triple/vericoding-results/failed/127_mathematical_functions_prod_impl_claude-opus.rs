// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_product_int_i8(a: Seq<i8>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int_i8(a.skip(1))
    }
}

proof fn lemma_product_zero(a: Seq<i8>, i: int)
    requires
        0 <= i < a.len(),
        a[i] == 0,
    ensures
        vec_product_int_i8(a) == 0,
    decreases a.len()
{
    if i == 0 {
        assert(a[0] == 0);
        assert(vec_product_int_i8(a) == 0 * vec_product_int_i8(a.skip(1)));
    } else {
        lemma_product_zero(a.skip(1), i - 1);
        assert(vec_product_int_i8(a) == (a[0] as int) * vec_product_int_i8(a.skip(1)));
        assert(vec_product_int_i8(a.skip(1)) == 0);
    }
}

proof fn lemma_product_map_equiv(a: Seq<i8>)
    ensures
        vec_product_int_i8(a) == vec_product_int(a.map(|i, x| x as i32)),
    decreases a.len()
{
    if a.len() == 0 {
        assert(a.map(|i, x| x as i32).len() == 0);
    } else {
        lemma_product_map_equiv(a.skip(1));
        assert(a.map(|i, x| x as i32)[0] == a[0] as i32);
        assert(a.skip(1).map(|i, x| x as i32) =~= a.map(|i, x| x as i32).skip(1));
    }
}
// </vc-helpers>

// <vc-spec>
spec fn vec_product_int(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int(a.skip(1))
    }
}

fn prod(a: Vec<i8>) -> (result: i8)
    ensures 
        result as int == vec_product_int(a@.map(|i, x| x as i32)),
        a.len() == 0 ==> result == 1,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result: i8 = 1;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result as int == vec_product_int_i8(a@.take(i as int)),
            forall|j: int| 0 <= j < i ==> a[j] != 0 ==> result != 0,
        decreases a.len() - i
    {
        let old_result = result;
        result = result * a[i];
        
        proof {
            assert(a@.take(i as int + 1) =~= a@.take(i as int).push(a@[i as int]));
            assert(vec_product_int_i8(a@.take(i as int + 1)) == 
                   vec_product_int_i8(a@.take(i as int)) * (a@[i as int] as int));
        }
        
        if a[i] == 0 {
            proof {
                lemma_product_zero(a@, i as int);
                lemma_product_map_equiv(a@);
            }
            return 0;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a@.take(a.len() as int) =~= a@);
        lemma_product_map_equiv(a@);
    }
    
    result
}
// </vc-code>


}
fn main() {}