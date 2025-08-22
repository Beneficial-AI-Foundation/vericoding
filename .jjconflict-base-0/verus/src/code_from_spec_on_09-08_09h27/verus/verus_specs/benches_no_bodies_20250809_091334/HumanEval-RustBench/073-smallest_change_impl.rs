use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end

spec fn diff(s: Seq<(i32, i32)>) -> (ret: int) {
    s.fold_left(
        0,
        |acc: int, x: (i32, i32)|
            if (x.0 != x.1) {
                acc + 1
            } else {
                acc
            },
    )
}
// pure-end

fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
{
    let first_half_len = v.len() / 2;
    let second_half_start = (v.len() + 1) / 2;
    let mut count = 0;
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause and fixed loop body indexing */
    while i < first_half_len
        invariant
            i <= first_half_len,
            first_half_len == v@.len() / 2,
            second_half_start == (v@.len() + 1) / 2,
            count == diff(zip_halves(v@).take(i as int)),
        decreases first_half_len - i
    {
        let j = v.len() - 1 - i;
        if v[i] != v[j] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}
fn main() {}