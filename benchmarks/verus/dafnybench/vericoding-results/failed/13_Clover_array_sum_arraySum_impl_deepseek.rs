use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_vec_indexing<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len() as int,
    ensures
        v[i as usize] == v@[i],
{
}

proof fn lemma_vec_len<T>(v: &Vec<T>)
    ensures
        v.len() as int == v@.len(),
{
}

proof fn lemma_vec_push<T>(v: &mut Vec<T>, x: T)
    ensures
        v@.len() == old(v)@.len() + 1,
        v@[old(v)@.len() as int] == x,
        forall|j: int| 0 <= j < old(v)@.len() ==> v@[j] == old(v)@[j],
{
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let mut c = Vec::with_capacity(a.len());
    let mut index: usize = 0;
    
    while index < a.len()
        invariant 
            0 <= index as int <= a.len() as int,
            c@.len() == index as nat,
            forall|j: int| 0 <= j < index as int ==> a@[j] + b@[j] == c@[j],
        decreases a.len() - index,
    {
        proof {
            lemma_vec_indexing(a, index as int);
            lemma_vec_indexing(b, index as int);
        }
        
        let sum = a[index] + b[index];
        c.push(sum);
        
        proof {
            lemma_vec_push(&mut c, sum);
        }
        
        index = index + 1;
    }
    
    proof {
        lemma_vec_len(&c);
    }
    c
}
// </vc-code>

fn main() {}

}