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
spec fn zip_halves_equiv<T>(v: Seq<T>, i: int) -> bool {
    i < (v.len() / 2) ==> (
        zip_halves(v)[i] == (v[i], v[v.len() - 1 - i])
    )
}

proof fn zip_halves_properties<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == (v.len() / 2),
        forall|i: int| 0 <= i < (v.len() / 2) ==> zip_halves(v)[i] == (v[i], v[v.len() - 1 - i]),
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    
    assert(first_half.len() == (v.len() / 2));
    assert(second_half.len() == (v.len() - ((v.len() + 1) / 2)));
    
    if v.len() % 2 == 0 {
        assert((v.len() + 1) / 2 == v.len() / 2);
        assert(second_half.len() == v.len() / 2);
    } else {
        assert((v.len() + 1) / 2 == v.len() / 2 + 1);
        assert(second_half.len() == v.len() / 2);
    }
}

proof fn diff_extend(s: Seq<(i32, i32)>, pair: (i32, i32))
    ensures diff(s.push(pair)) == diff(s) + (if pair.0 != pair.1 { 1int } else { 0int })
{
    let f = |acc: int, x: (i32, i32)| if (x.0 != x.1) { acc + 1 } else { acc };
    assert(s.push(pair).fold_left(0, f) == f(s.fold_left(0, f), pair));
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
    if v.len() == 0 {
        return 0;
    }
    
    let half_len = v.len() / 2;
    let mut change: usize = 0;
    let mut i = 0;
    
    proof {
        zip_halves_properties(v@);
    }
    
    while i < half_len
        invariant
            i <= half_len,
            half_len == v@.len() / 2,
            change == diff(zip_halves(v@).take(i as int)),
            v@.len() < usize::MAX,
            change <= v@.len(),
        decreases half_len - i
    {
        let left_val = v[i];
        let right_val = v[v.len() - 1 - i];
        
        if left_val != right_val {
            change = change + 1;
        }
        
        proof {
            let zipped = zip_halves(v@);
            let current_pair = zipped[i as int];
            assert(current_pair == (v@[i as int], v@[(v@.len() - 1 - i as int) as int]));
            assert(current_pair == (left_val, right_val));
            
            let prev_take = zipped.take(i as int);
            let next_take = zipped.take((i + 1) as int);
            assert(next_take == prev_take.push(current_pair));
            
            diff_extend(prev_take, current_pair);
            assert(diff(next_take) == diff(prev_take) + (if current_pair.0 != current_pair.1 { 1int } else { 0int }));
        }
        
        i = i + 1;
    }
    
    proof {
        let zipped = zip_halves(v@);
        assert(zipped.take(half_len as int) == zipped);
        assert(change == diff(zipped));
    }
    
    change
}
// </vc-code>

}
fn main() {}