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
spec fn zip_halves_len_lemma<T>(v: Seq<T>)
    ensures zip_halves(v).len() == v.len() / 2
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    assert(first_half.len() == v.len() / 2);
    assert(second_half.len() == v.len() - ((v.len() + 1) / 2));
    assert(v.len() - ((v.len() + 1) / 2) == (v.len() / 2));
}

proof fn diff_empty_lemma()
    ensures diff(Seq::<(i32, i32)>::empty()) == 0int
{
}

proof fn diff_push_lemma(s: Seq<(i32, i32)>, x: (i32, i32))
    ensures diff(s.push(x)) == diff(s) + if x.0 != x.1 { 1int } else { 0int }
{
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
    
    let mut change = 0;
    let mut i = 0;
    
    while i < first_half_len
        invariant
            i <= first_half_len,
            first_half_len == len / 2,
            second_half_start == (len + 1) / 2,
            len == v@.len(),
            change == diff(zip_halves(v@.take(i as int + first_half_len as int)).take(i as int)),
        decreases first_half_len - i,
    {
        let first_elem = v[i];
        let second_elem = v[len - 1 - i];
        
        if first_elem != second_elem {
            change += 1;
        }
        
        proof {
            let current_pair = (first_elem, second_elem);
            let prev_zipped = zip_halves(v@.take(i as int + first_half_len as int)).take(i as int);
            let next_zipped = zip_halves(v@.take(i as int + 1 + first_half_len as int)).take(i as int + 1);
            diff_push_lemma(prev_zipped, current_pair);
        }
        
        i += 1;
    }
    
    proof {
        assert(i == first_half_len);
        assert(zip_halves(v@).len() == first_half_len) by {
            zip_halves_len_lemma(v@);
        }
        assert(zip_halves(v@.take(first_half_len as int + first_half_len as int)).take(first_half_len as int) == zip_halves(v@));
    }
    
    change
}
// </vc-code>

}
fn main() {}