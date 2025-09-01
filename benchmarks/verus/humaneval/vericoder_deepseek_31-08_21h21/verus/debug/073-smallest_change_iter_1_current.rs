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
        (n + 1) / 2 == n / 2 + (if n % 2 == 0 { 0 } else { 1 }),
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
    assert(v.skip(((v.len() + 1) / 2) as int).reverse().len() == v.len() / 2);
}

proof fn lemma_skip_reverse_length<T>(v: Seq<T>)
    ensures
        v.skip(((v.len() + 1) / 2) as int).reverse().len() == v.len() / 2,
{
    lemma_div_plus_one_mod_two(v.len() as nat);
    assert(v.skip(((v.len() + 1) / 2) as int).len() == v.len() / 2);
}

spec fn seq_index<T>(s: Seq<T>, i: int) -> T {
    s[i]
}

proof fn lemma_zip_halves_index<T>(v: Seq<T>, i: int)
    requires
        0 <= i < v.len() / 2,
    ensures
        zip_halves(v)@[i] == (v@[i], v@[v.len() - 1 - i]),
{
    lemma_div_plus_one_mod_two(v.len() as nat);
    assert(v.skip(((v.len() + 1) / 2) as int).reverse()@[i] == v@[v.len() - 1 - i]);
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
    let mut i = 0;
    
    while i < half
        invariant
            i <= half,
            change == diff(zip_halves(v@.take(i as int).concat(v@.skip(i as int)))),
    {
        let left = v[i];
        let right = v[n - 1 - i];
        
        proof {
            lemma_zip_halves_index(v@, i as int);
            assert(zip_halves(v@)@[i as int] == (left, right));
        }
        
        if left != right {
            change += 1;
        }
        
        i += 1;
        
        proof {
            assert(zip_halves(v@).take(i as int) == zip_halves(v@.take(i as int).concat(v@.skip(i as int))));
            assert(change == diff(zip_halves(v@).take(i as int)));
        }
    }
    
    proof {
        lemma_zip_halves_length(v@);
        assert(zip_halves(v@).take(half as int) == zip_halves(v@));
        assert(change == diff(zip_halves(v@)));
    }
    
    change
}
// </vc-code>

fn main() {}
}