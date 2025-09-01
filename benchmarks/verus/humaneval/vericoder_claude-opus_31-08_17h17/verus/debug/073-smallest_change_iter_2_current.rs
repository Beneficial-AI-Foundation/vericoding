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
        zip_halves(v).len() == v.len() / 2,
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half = v.skip(((v.len() + 1) / 2) as int).reverse();
    assert(first_half.len() == v.len() / 2);
    assert(second_half.len() == v.len() - (v.len() + 1) / 2);
    assert(v.len() - (v.len() + 1) / 2 == v.len() / 2);
}

proof fn diff_step(s: Seq<(i32, i32)>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        diff(s.take(i + 1)) == diff(s.take(i)) + if s[i].0 != s[i].1 { 1int } else { 0int },
{
    let s_prefix = s.take(i);
    let s_prefix_plus = s.take(i + 1);
    assert(s_prefix_plus =~= s_prefix.push(s[i]));
}

proof fn diff_empty()
    ensures
        diff(Seq::<(i32, i32)>::empty()) == 0,
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
    let n = v.len();
    let half = n / 2;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < half
        invariant
            i <= half,
            half == n / 2,
            n == v@.len(),
            count == diff(zip_halves(v@).take(i as int)),
    {
        let j = n - 1 - i;
        let left = v[i];
        let right = v[j];
        
        assert(zip_halves(v@).len() == half as int) by {
            zip_halves_len(v@);
        }
        
        assert(i < zip_halves(v@).len());
        
        let zipped = zip_halves(v@);
        assert(zipped[i as int] == (v@[i as int], v@[j as int])) by {
            let first_half = v@.take((v@.len() / 2) as int);
            let second_half_rev = v@.skip(((v@.len() + 1) / 2) as int).reverse();
            assert(first_half[i as int] == v@[i as int]);
            let skip_point = (v@.len() + 1) / 2;
            assert(j as int == v@.len() - 1 - i as int);
            assert(second_half_rev[i as int] == v@[j as int]);
        }
        
        if left != right {
            count = count + 1;
            assert(diff(zipped.take((i + 1) as int)) == diff(zipped.take(i as int)) + 1int) by {
                diff_step(zipped, i as int);
            }
        } else {
            assert(diff(zipped.take((i + 1) as int)) == diff(zipped.take(i as int))) by {
                diff_step(zipped, i as int);
            }
        }
        
        i = i + 1;
    }
    
    assert(zip_halves(v@).take(half as int) =~= zip_halves(v@)) by {
        zip_halves_len(v@);
    }
    
    count
}
// </vc-code>

fn main() {}
}