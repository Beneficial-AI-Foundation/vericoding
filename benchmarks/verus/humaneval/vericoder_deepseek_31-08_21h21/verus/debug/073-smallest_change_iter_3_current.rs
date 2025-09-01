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
        zip_halves(v).subrange(0, i) == zip_halves(v.subrange(0, i).add(v.subrange(v.len() - i, v.len()))),
{
    if i == 0 {
        lemma_subrange_empty(zip_halves(v), 0);
        assert(zip_halves(v.subrange(0, 0).add(v.subrange(v.len(), v.len()))) == zip_halves(Seq::empty()));
        assert(zip_halves(Seq::empty()).len() == 0);
    } else {
        lemma_zip_halves_subrange(v, (i - 1) as nat);
        assert(zip_halves(v).subrange(0, i - 1) == zip_halves(v.subrange(0, i - 1).add(v.subrange(v.len() - (i - 1), v.len()))));
        
        let s1 = v.subrange(0, i - 1).add(v.subrange(v.len() - (i - 1), v.len()));
        let s2 = v.subrange(0, i).add(v.subrange(v.len() - i, v.len()));
        
        lemma_subrange_merge(v, 0, i - 1, i);
        lemma_subrange_merge(v, v.len() - i, v.len() - (i - 1), v.len());
        
        assert(s2 == s1.add(v.subrange(i - 1, i)).add(v.subrange(v.len() - i, v.len() - (i - 1))));
        
        lemma_zip_halves_index(v, (i - 1) as int);
        assert(zip_halves(v).index((i - 1) as int) == (v.index((i - 1) as int), v.index(v.len() - 1 - (i - 1))));
    }
}

proof fn lemma_diff_subrange<T>(s: Seq<(T, T)>, i: nat)
    requires
        i <= s.len(),
    ensures
        diff(s) == diff(s.subrange(0, i)) + diff(s.subrange(i, s.len())),
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(diff(s.subrange(0, 0)) == 0);
    } else {
        lemma_diff_subrange(s, (i - 1) as nat);
        assert(diff(s) == diff(s.subrange(0, i - 1)) + diff(s.subrange(i - 1, s.len())));
        assert(diff(s.subrange(i - 1, s.len())) == diff(s.subrange(i - 1, i)) + diff(s.subrange(i, s.len())));
        assert(diff(s.subrange(0, i)) == diff(s.subrange(0, i - 1)) + diff(s.subrange(i - 1, i)));
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
            change == diff(zip_halves(v@).subrange(0, i as nat)),
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
            assert(diff(zip_halves(v@).subrange(0, i as nat)) == diff(zip_halves(v@).subrange(0, (i - 1) as nat)) + diff(zip_halves(v@).subrange((i - 1) as nat, i as nat)));
            assert(zip_halves(v@).subrange((i - 1) as nat, i as nat).len() == 1);
            assert(zip_halves(v@).subrange((i - 1) as nat, i as nat).index(0) == (left, right));
            assert(diff(zip_halves(v@).subrange((i - 1) as nat, i as nat)) == if left != right { 1 } else { 0 });
        }
    }
    
    proof {
        lemma_zip_halves_length(v@);
        assert(zip_halves(v@).subrange(0, half as nat) == zip_halves(v@));
        assert(change == diff(zip_halves(v@)));
    }
    
    change
}
// </vc-code>

fn main() {}
}