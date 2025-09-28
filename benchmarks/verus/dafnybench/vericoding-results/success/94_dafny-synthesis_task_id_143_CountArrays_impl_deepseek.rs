use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn len_nonnegative<T>(v: &Vec<T>)
    ensures
        v.len() >= 0,
{
}

proof fn vec_len_equals_seq_len<T>(v: &Vec<T>)
    ensures
        v.len() == v@.len(),
{
}

proof fn seq_len_nonnegative<T>(s: Seq<T>)
    ensures
        s.len() >= 0,
{
}
// </vc-helpers>

// <vc-spec>
fn count_arrays(arrays: &Vec<Vec<i32>>) -> (count: usize)
    ensures 
        count >= 0,
        count == arrays.len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    assert(arrays@.len() >= 0) by { seq_len_nonnegative(arrays@); };
    while i < arrays.len()
        invariant
            i <= arrays.len(),
            count == i,
            count >= 0,
        decreases arrays.len() - i,
    {
        count = count + 1;
        i = i + 1;
    }
    assert(count == arrays.len()) by {
        vec_len_equals_seq_len(arrays);
    };
    count
}
// </vc-code>

fn main() {
}

}