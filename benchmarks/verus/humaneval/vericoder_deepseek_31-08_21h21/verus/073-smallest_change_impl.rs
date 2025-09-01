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
proof fn lemma_div_plus_one_mod_two(n: nat)
    requires
        n >= 0,
    ensures
        (n + 1) / 2 == n / 2 + (if n % 2 == 0 { 0nat } else { 1nat }),
{
    if n % 2 == 0 {
        assert((n + 1) / 2 == n / 2);
    } else {
        assert((n + 1) / 2 == n / 2 + 1);
    }
}

proof fn lemma_zip_halves_length<T>(v: Seq<T>)
    ensures
        zip_halves(v).len() == v.len() / 2,
{
    assert(v.take((v.len() / 2) as int).len() == v.len() / 2);
    lemma_skip_reverse_length(v);
}

proof fn lemma_skip_reverse_length<T>(v: Seq<T>)
    ensures
        v.skip(((v.len() + 1) / 2) as int).reverse().len() == v.len() / 2,
{
    lemma_div_plus_one_mod_two(v.len() as nat);
    assert(v.skip(((v.len() + 1) / 2) as int).len() == v.len() / 2);
}

proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < v.len() / 2,
    ensures
        zip_halves(v).index(i) == (v.index(i), v.index(v.len() - 1 - i)),
{
    lemma_div_plus_one_mod_two(v.len() as nat);
    assert(v.skip(((v.len() + 1) / 2) as int).reverse().index(i) == v.index(v.len() - 1 - i));
}

proof fn lemma_subrange_empty<T>(v: Seq<T>, i: int)
    requires
        0 <= i <= v.len(),
    ensures
        v.subrange(i, i).len() == 0,
{
}

proof fn lemma_subrange_merge<T>(v: Seq<T>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= v.len(),
    ensures
        v.subrange(i, j).add(v.subrange(j, k)) == v.subrange(i, k),
{
}

proof fn lemma_zip_halves_subrange<T>(v: Seq<T>, i: nat)
    requires
        i <= v.len() / 2,
    ensures
        zip_halves(v).subrange(0, i as int) == zip_halves(v.subrange(0, i as int).add(v.subrange((v.len() - i as int) as int, v.len() as int))),
{
    if i == 0 {
        lemma_subrange_empty(zip_halves(v), 0);
        assert(zip_halves(v.subrange(0, 0).add(v.subrange(v.len() as int, v.len() as int))) == zip_halves(Seq::empty()));
        assert(zip_halves(Seq::empty()).len() == 0);
    } else {
        lemma_zip_halves_subrange(v, (i - 1) as nat);
        assert(zip_halves(v).subrange(0, (i - 1) as int) == zip_halves(v.subrange(0, (i - 1) as int).add(v.subrange((v.len() - (i - 1) as int) as int, v.len() as int))));
        
        let s1 = v.subrange(0, (i - 1) as int).add(v.subrange((v.len() - (i - 1) as int) as int, v.len() as int));
        let s2 = v.subrange(0, i as int).add(v.subrange((v.len() - i as int) as int, v.len() as int));
        
        lemma_subrange_merge(v, 0, (i - 1) as int, i as int);
        lemma_subrange_merge(v, (v.len() - i as int) as int, (v.len() - (i - 1) as int) as int, v.len() as int);
        
        assert(s2 == s1.add(v.subrange((i - 1) as int, i as int)).add(v.subrange((v.len() - i as int) as int, (v.len() - (i - 1) as int) as int)));
        
        lemma_zip_halves_index(v, (i - 1) as int);
        assert(zip_halves(v).index((i - 1) as int) == (v.index((i - 1) as int), v.index(v.len() - 1 - (i - 1))));
    }
}

proof fn lemma_diff_subrange(s: Seq<(i32, i32)>, i: nat)
    requires
        i <= s.len(),
    ensures
        diff(s) == diff(s.subrange(0, i as int)) + diff(s.subrange(i as int, s.len() as int)),
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(diff(s.subrange(0, 0)) == 0);
    } else {
        lemma_diff_subrange(s, (i - 1) as nat);
        assert(diff(s) == diff(s.subrange(0, (i - 1) as int)) + diff(s.subrange((i - 1) as int, s.len() as int)));
        assert(diff(s.subrange((i - 1) as int, s.len() as int)) == diff(s.subrange((i - 1) as int, i as int)) + diff(s.subrange(i as int, s.len() as int)));
        assert(diff(s.subrange(0, i as int)) == diff(s.subrange(0, (i - 1) as int)) + diff(s.subrange((i - 1) as int, i as int)));
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
    let n = v.len();
    let half = n / 2;
    let mut change = 0;
    let mut i: usize = 0;
    
    while i < half
        invariant
            i <= half,
            change == diff(zip_halves(v@).subrange(0, i as int)),
    {
        let left = v[i];
        let right = v[n - 1 - i];
        
        proof {
            lemma_zip_halves_index(v@, i as int);
            assert(zip_halves(v@).index(i as int) == (left, right));
        }
        
        if left != right {
            change += 1;
        }
        
        i += 1;
        
        proof {
            lemma_diff_subrange(zip_halves(v@), i as nat);
            assert(diff(zip_halves(v@).subrange(0, i as int)) == diff(zip_halves(v@).subrange(0, (i - 1) as int)) + diff(zip_halves(v@).subrange((i - 1) as int, i as int)));
            assert(zip_halves(v@).subrange((i - 1) as int, i as int).len() == 1);
            assert(zip_halves(v@).subrange((i - 1) as int, i as int).index(0) == (left, right));
            assert(diff(zip_halves(v@).subrange((i - 1) as int, i as int)) == if left != right { 1int } else { 0int });
        }
    }
    
    proof {
        lemma_zip_halves_length(v@);
        assert(zip_halves(v@).subrange(0, half as int) == zip_halves(v@));
        assert(change == diff(zip_halves(v@)));
    }
    
    change
}
// </vc-code>

fn main() {}
}