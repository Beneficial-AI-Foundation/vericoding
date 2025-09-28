use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn array_product_lemma(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>, i: int)
    requires 
        a.len() == b.len(),
        a.len() == c.len(),
        0 <= i <= a.len(),
        forall|j: int| 0 <= j < i ==> a[j] * b[j] == c[j]
    ensures 
        forall|j: int| 0 <= j < i ==> a[j] * b[j] == c[j]
{
}

spec fn seq_from_slice(slice: &[i32]) -> Seq<i32>
    recommends
        slice.len() as int >= 0,
    decreases slice.len() as int,
{
    if slice.is_empty() {
        Seq::empty()
    } else {
        let rest_slice = &slice[1..];
        seq_from_slice(rest_slice).push(slice[0])
    }
}

spec fn seq_from_vec(vec: &Vec<i32>) -> Seq<i32>
    decreases vec.len() as int,
{
    if vec.is_empty() {
        Seq::empty()
    } else {
        let mut result = Seq::empty();
        let mut i: int = 0;
        while i < vec.len() as int
            invariant
                0 <= i <= vec.len() as int,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result[j] == vec@[j],
        {
            result = result.push(vec@[i]);
            i = i + 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut c = Vec::<i32>::with_capacity(len);
    let mut n: usize = 0;
    
    while n < len
        invariant 
            0 <= n <= len,
            c.len() == n,
            forall|i: int| 0 <= i < n ==> a[i] * b[i] == c@[i]
    {
        let product = a[n] * b[n];
        c.push(product);
        proof {
            let a_seq = seq_from_slice(a);
            let b_seq = seq_from_slice(b);
            let c_seq = seq_from_vec(&c);
            array_product_lemma(a_seq, b_seq, c_seq, n as int);
        }
        n = n + 1;
    }
    
    c
}
// </vc-code>

fn main() {}

}