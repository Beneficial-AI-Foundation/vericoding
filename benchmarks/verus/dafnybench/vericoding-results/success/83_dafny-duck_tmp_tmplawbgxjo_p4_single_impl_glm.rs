use vstd::prelude::*;

verus! {

//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>
proof fn lemma_subrange_append<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i) + seq![s[i]] == s.subrange(0, i+1)
{
    assert(s.subrange(0, i+1) == s.subrange(0, i) + s.subrange(i, i+1));
    assert(s.subrange(i, i+1) == seq![s[i]]);
}
// </vc-helpers>

// <vc-spec>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
// </vc-spec>
// <vc-code>
{
    let mut b = Vec::new();
    for i in 0..x.len()
        invariant
            b@.len() == i,
            b@ == x@.subrange(0, i as int),
    {
        b.push(x[i]);
    }
    for j in 0..y.len()
        invariant
            b@.len() == x.len() + j,
            b@ == x@ + y@.subrange(0, j as int),
    {
        b.push(y[j]);
        proof {
            lemma_subrange_append(y@, j as int);
        }
    }
    b
}
// </vc-code>

fn main() {
}

}