use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_pairwise_addition_index(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len() / 2,
    ensures
        2*i + 1 < a.len(),
{
    assert(2*i + 1 < 2*(a.len() / 2));
    assert(2*(a.len() / 2) <= a.len());
}

proof fn lemma_vec_to_seq<T>(v: &Vec<T>) -> (s: Seq<T>)
    ensures
        s.len() == v.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == v@[i],
{
    v@
}

proof fn lemma_div_mod(index: int)
    requires
        index % 2 == 0,
    ensures
        (index + 2) % 2 == 0,
{
}

proof fn lemma_index_range(a: Seq<i32>, index: int)
    requires
        index >= 0,
        index + 1 < a.len(),
    ensures
        index < a.len(),
        index + 1 < a.len(),
{
}

proof fn lemma_div_properties(len: int, index: int)
    requires
        index >= 0,
        len % 2 == 0,
        index <= len,
        index % 2 == 0,
    ensures
        index / 2 <= len / 2,
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
    let mut result = Vec::with_capacity(a.len() / 2);
    let mut index = 0;
    
    while index < a.len()
        invariant
            0 <= index <= a.len(),
            index % 2 == 0,
            result.len() == index / 2,
            forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
        decreases a.len() - index,
    {
        proof {
            lemma_div_properties(a.len() as int, index as int);
        }
        
        if index + 1 < a.len() {
            proof {
                lemma_index_range(a@, index as int);
            }
            let sum = a[index] + a[index + 1];
            result.push(sum);
            proof {
                lemma_pairwise_addition_index(a@, (index / 2) as int);
            }
        }
        index = index + 2;
    }
    
    result
}
// </vc-code>

fn main() {}

}