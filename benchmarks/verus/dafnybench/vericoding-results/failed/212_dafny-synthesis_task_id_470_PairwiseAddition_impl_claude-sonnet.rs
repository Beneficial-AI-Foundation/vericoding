use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_even_less_than_even(a: usize, b: usize)
    requires
        a % 2 == 0,
        a < b,
        b % 2 == 0,
    ensures
        a + 1 < b,
{
}

fn lemma_addition_bounds(x: i32, y: i32)
    ensures
        (x as i64) + (y as i64) >= i32::MIN as i64,
        (x as i64) + (y as i64) <= i32::MAX as i64,
{
}
// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i % 2 == 0,
            i <= a.len(),
            result.len() == i / 2,
            forall|j: int| 0 <= j < result.len() ==> result[j as int] == a[2*j] + a[2*j + 1],
        decreases a.len() - i,
    {
        assert(a.len() % 2 == 0);
        assert(i < a.len());
        assert(i % 2 == 0);
        lemma_even_less_than_even(i, a.len());
        assert(i + 1 < a.len());
        
        let val1 = a[i];
        let val2 = a[i + 1];
        lemma_addition_bounds(val1, val2);
        let val1_i64 = val1 as i64;
        let val2_i64 = val2 as i64;
        let sum_i64 = val1_i64 + val2_i64;
        assert(sum_i64 >= i32::MIN as i64 && sum_i64 <= i32::MAX as i64);
        let sum = sum_i64 as i32;
        result.push(sum);
        i += 2;
    }
    
    result
}
// </vc-code>

fn main() {}

}