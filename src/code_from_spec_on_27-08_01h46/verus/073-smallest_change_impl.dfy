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
proof fn zip_halves_len<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == (v.len() / 2) as int,
{
}

proof fn zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < zip_halves(v).len(),
    ensures
        zip_halves(v)[i].0 == v[i],
        zip_halves(v)[i].1 == v[v.len() as int - 1 - i],
{
}

proof fn diff_empty()
    ensures
        diff(Seq::<(i32, i32)>::empty()) == 0,
{
}

proof fn diff_push(s: Seq<(i32, i32)>, x: (i32, i32))
    ensures
        diff(s.push(x)) == diff(s) + if x.0 != x.1 { 1int } else { 0int },
{
    assert(s.push(x).fold_left(
        0,
        |acc: int, y: (i32, i32)|
            if (y.0 != y.1) {
                acc + 1
            } else {
                acc
            },
    ) == s.fold_left(
        0,
        |acc: int, y: (i32, i32)|
            if (y.0 != y.1) {
                acc + 1
            } else {
                acc
            },
    ) + if x.0 != x.1 { 1int } else { 0int });
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
    let half_len = len / 2;
    
    let mut change = 0;
    let mut i = 0;
    
    while i < half_len
        invariant
            0 <= i <= half_len,
            half_len == len / 2,
            len == v.len(),
            change == diff(zip_halves(v@).take(i as int)),
            i < len,
        decreases
            half_len - i,
    {
        let left_idx = i;
        let right_idx = len - 1 - i;
        
        assert(left_idx < v.len());
        assert(right_idx < v.len());
        
        if v[left_idx] != v[right_idx] {
            change = change + 1;
        }
        
        proof {
            let zipped = zip_halves(v@);
            let current_pair = (v@[left_idx as int], v@[right_idx as int]);
            
            assert(left_idx as int < v@.len());
            assert(right_idx as int < v@.len());
            
            diff_push(zipped.take(i as int), current_pair);
            
            assert(zipped.take((i + 1) as int) == zipped.take(i as int).push(zipped[i as int]));
            assert(zipped[i as int] == current_pair) by {
                zip_halves_index(v@, i as int);
            };
        }
        
        i = i + 1;
    }
    
    proof {
        assert(zip_halves(v@).take(half_len as int) == zip_halves(v@)) by {
            zip_halves_len(v@);
        };
    }
    
    change
}
// </vc-code>

}
fn main() {}