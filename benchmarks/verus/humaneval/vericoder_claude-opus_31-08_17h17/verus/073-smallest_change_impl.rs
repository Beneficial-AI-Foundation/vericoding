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
    
    // Use the fold_left definition to prove the postcondition
    let fold_fn = |acc: int, x: (i32, i32)| if x.0 != x.1 { acc + 1 } else { acc };
    assert(diff(s_prefix_plus) == s_prefix_plus.fold_left(0, fold_fn));
    assert(diff(s_prefix) == s_prefix.fold_left(0, fold_fn));
    
    // The fold_left of s_prefix_plus is the fold_left of s_prefix followed by one more element
    assert(s_prefix_plus.fold_left(0, fold_fn) == fold_fn(s_prefix.fold_left(0, fold_fn), s[i]));
    assert(fold_fn(diff(s_prefix), s[i]) == diff(s_prefix) + if s[i].0 != s[i].1 { 1int } else { 0int });
}

proof fn diff_empty()
    ensures
        diff(Seq::<(i32, i32)>::empty()) == 0,
{
}

proof fn zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < v.len() / 2,
    ensures
        zip_halves(v)[i] == (v[i], v[v.len() - 1 - i]),
{
    let first_half = v.take((v.len() / 2) as int);
    let second_half_rev = v.skip(((v.len() + 1) / 2) as int).reverse();
    assert(first_half[i] == v[i]);
    let skip_point = (v.len() + 1) / 2;
    assert(second_half_rev[i] == v[v.len() - 1 - i]);
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
            count <= i,  // Add upper bound for count to prevent overflow
            count == diff(zip_halves(v@).take(i as int)),
        decreases half - i,
    {
        let j = n - 1 - i;
        let left = v[i];
        let right = v[j];
        
        assert(zip_halves(v@).len() == half as int) by {
            zip_halves_len(v@);
        }
        
        assert(i < zip_halves(v@).len());
        
        assert(zip_halves(v@)[i as int] == (v@[i as int], v@[j as int])) by {
            zip_halves_index(v@, i as int);
        }
        
        let old_count = count;
        
        if left != right {
            assert(count < usize::MAX) by {
                assert(count <= i);
                assert(i < half);
                assert(half <= n);
                assert(n < usize::MAX);
            }
            count = count + 1;
            assert(diff(zip_halves(v@).take((i + 1) as int)) == diff(zip_halves(v@).take(i as int)) + 1int) by {
                diff_step(zip_halves(v@), i as int);
                assert(zip_halves(v@)[i as int].0 == left);
                assert(zip_halves(v@)[i as int].1 == right);
                assert(left != right);
            }
        } else {
            assert(diff(zip_halves(v@).take((i + 1) as int)) == diff(zip_halves(v@).take(i as int))) by {
                diff_step(zip_halves(v@), i as int);
                assert(zip_halves(v@)[i as int].0 == left);
                assert(zip_halves(v@)[i as int].1 == right);
                assert(left == right);
            }
        }
        
        assert(count == diff(zip_halves(v@).take((i + 1) as int))) by {
            assert(old_count == diff(zip_halves(v@).take(i as int)));
            if left != right {
                assert(count == old_count + 1);
                assert(diff(zip_halves(v@).take((i + 1) as int)) == diff(zip_halves(v@).take(i as int)) + 1int);
            } else {
                assert(count == old_count);
                assert(diff(zip_halves(v@).take((i + 1) as int)) == diff(zip_halves(v@).take(i as int)));
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