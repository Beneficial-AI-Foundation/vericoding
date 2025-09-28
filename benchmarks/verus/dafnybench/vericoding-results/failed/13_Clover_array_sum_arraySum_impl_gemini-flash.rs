use vstd::prelude::*;

verus! {

// <vc-helpers>
fn add_vec_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires
        a.len() == b.len(),
    ensures
        c.len() == a.len(),
        forall|i: int| #![trigger c.nth(i)] 0 <= i && (i as nat) < a.len() ==> a.nth(i).unwrap() + b.nth(i).unwrap() == c.nth(i).unwrap(),
{
    let mut c: Vec<i32> = Vec::new();
    let len_nat = a.len();

    // Proven to be safe here that 'len' is non-negative and can be used as upper bound for 'i'
    assert(len_nat >= 0);

    let mut i: nat = 0;
    while i < len_nat
        invariant
            i <= len_nat,
            c.len() == i,
            forall|j: int| #![trigger c.nth(j)] 0 <= j && (j as nat) < i ==> a.nth(j).unwrap() + b.nth(j).unwrap() == c.nth(j).unwrap(),
    {
        c.push(a.index(i as usize) + b.index(i as usize));
        i = i + 1;
    }
    c
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
    add_vec_elements(a, b)
}
// </vc-code>

fn main() {}

}