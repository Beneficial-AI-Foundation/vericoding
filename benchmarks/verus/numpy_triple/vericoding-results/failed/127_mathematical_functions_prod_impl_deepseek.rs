// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_vec_product_zero(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
        a[i] == 0
    ensures
        vec_product_int(a) == 0
    decreases a.len()
{
    if i == 0 {
    } else {
        lemma_vec_product_zero(a.skip(1), i - 1);
    }
}

proof fn lemma_vec_product_skip_consistency(a: Seq<i32>, idx: int)
    requires
        0 <= idx <= a.len()
    ensures
        vec_product_int(a.subrange(0, idx)) == vec_product_int_fixed(a.subrange(0, idx))
    decreases idx
{
    if idx == 0 {
        assert(vec_product_int(a.subrange(0, 0)) == 1);
        assert(vec_product_int_fixed(a.subrange(0, 0)) == 1);
    } else {
        lemma_vec_product_skip_consistency(a, idx - 1);
        assert(vec_product_int(a.subrange(0, idx)) == (a[idx-1] as int) * vec_product_int(a.subrange(0, idx-1)));
        assert(vec_product_int_fixed(a.subrange(0, idx)) == (a[idx-1] as int) * vec_product_int_fixed(a.subrange(0, idx-1)));
    }
}

spec fn vec_product_int_fixed(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        1
    } else {
        (a[0] as int) * vec_product_int_fixed(a.skip(1))
    }
}

proof fn lemma_product_zero_exists(a: Seq<i32>, idx: int)
    requires
        0 <= idx <= a.len()
    ensures
        (exists|j: int| 0 <= j < a.len() && a[j] == 0) ==> 
            vec_product_int_fixed(a.subrange(0, idx)) == 0
    decreases a.len() - idx
{
    if idx < a.len() {
        if a[idx] == 0 {
            lemma_vec_product_zero(a.subrange(0, idx+1), idx);
        } else {
            lemma_product_zero_exists(a, idx + 1);
        }
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
    /* code modified by LLM (iteration 5): fixed proof block compilation error */
    if a.len() == 0 {
        return 1;
    }
    
    let mut result: i8 = 1;
    let mut idx: usize = 0;
    let mut has_zero = false;
    
    while idx < a.len()
        invariant
            result as int == vec_product_int_fixed(a@.subrange(0, idx as int).map(|j: int, x: i8| x as i32)),
            0 <= idx <= a.len(),
            has_zero == (exists|j: int| 0 <= j < idx && a[j] == 0),
            has_zero ==> result == 0
        decreases a.len() - idx
    {
        let current = a[idx];
        
        if current == 0 {
            result = 0;
            has_zero = true;
        } else if !has_zero {
            let temp = (result as i16) * (current as i16);
            if temp < -128 || temp > 127 {
                result = if temp > 0 { 127 } else { -128 };
            } else {
                result = temp as i8;
            }
        }
        
        idx = idx + 1;
        
        proof { 
            lemma_vec_product_skip_consistency(a@.map(|i, x| x as i32), idx as int);
            lemma_product_zero_exists(a@.map(|i, x| x as i32), idx as int);
        }
    }
    
    proof { lemma_vec_product_skip_consistency(a@.map(|i, x| x as i32), a.len() as int); }
    result
}
// </vc-code>


}
fn main() {}