use vstd::prelude::*;

verus! {

spec fn zip_halves<T>(v: Seq<T>) -> (ret: Seq<(T, T)>) {
    v.take((v.len() / 2) as int).zip_with(v.skip(((v.len() + 1) / 2) as int).reverse())
}
// pure-end
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

// <vc-helpers>
proof fn lemma_fold_left_diff_distributes(s1: Seq<(i32, i32)>, s2: Seq<(i32, i32)>)
    ensures diff(s1 + s2) == diff(s1) + diff(s2)
{
    assert(s1 + s2 == s1.add(s2));
}

proof fn lemma_diff_single(x: (i32, i32))
    ensures diff(seq![x]) == if x.0 != x.1 { 1int } else { 0int }
{
}

proof fn lemma_diff_non_negative(s: Seq<(i32, i32)>)
    ensures diff(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_diff_non_negative(s.drop_last());
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_change(v: Vec<i32>) -> (change: usize)
    // pre-conditions-start
    requires
        v@.len() < usize::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        change == diff(zip_halves(v@)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let len = v.len();
    let first_half_len = len / 2;
    let second_half_start = (len + 1) / 2;
    
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < first_half_len
        invariant
            i <= first_half_len,
            first_half_len == len / 2,
            second_half_start == (len + 1) / 2,
            count == diff(zip_halves(v@).take(i as int)),
            len == v@.len(),
        decreases first_half_len - i
    {
        let first_idx = i;
        let second_idx = len - 1 - i;
        
        if v[first_idx] != v[second_idx] {
            count = count + 1;
        }
        
        i = i + 1;
        
        proof {
            assert(zip_halves(v@).take((i - 1) as int).push(zip_halves(v@)[(i - 1) as int]) == zip_halves(v@).take(i as int));
        }
    }
    
    proof {
        assert(zip_halves(v@).take(first_half_len as int) == zip_halves(v@));
        lemma_diff_non_negative(zip_halves(v@));
    }
    
    count
}
// </vc-code>

}
fn main() {}