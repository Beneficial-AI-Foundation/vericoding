use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
proof fn seq_swap_preserves_multiset(s: Seq<i32>, i: usize, j: usize)
    requires i < s.len() && j < s.len()
    ensures (s.update(i, s[j]).update(j, s[i])).to_multiset() == s.to_multiset()
{
    let s2 = s.update(i, s[j]).update(j, s[i]);
    assert(forall|k: int|
        0 <= k && (k as usize) < s.len() ==>
            s2[k as usize] == if (k as usize) == i {
                s[j]
            } else if (k as usize) == j {
                s[i]
            } else {
                s[k as usize]
            }
    );

    assert(forall|x: i32| #[trigger s] {
            let lhs = s2.to_multiset().count(x);
            let rhs = s.to_multiset().count(x);
            lhs == rhs
    });

    assert(s2.to_multiset() == s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// <vc-code>
{
    let n = v.len();
    let old_v: Seq<i32> = v@;

    let mut pos: Vec<i32> = Vec::new();
    let mut neg: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant j <= n,
        invariant pos.len() + neg.len() == j,
        invariant forall|x: i32| #[trigger old_v] pos@.to_multiset().count(x) + neg@.to_multiset().count(x) == old_v.subrange(0, j as int).to_multiset().count(x),
        invariant forall|u: int| 0 <= u && u < pos@.len() ==> pos@[u] >= 0,
        invariant forall|u: int| 0 <= u && u < neg@.len() ==> neg@[u] < 0
    {
        let val: i32 = old_v[j as int];
        if val >= 0 {
            pos.push(val);
        } else {
            neg.push(val);
        }
        j += 1;
    }

    // After partitioning, pos.len() + neg.len() == n and counts match old_v[0..n)
    assert(pos.len() + neg.len() == n);
    assert(forall|x: i32| #[trigger old_v] pos@.to_multiset().count(x) + neg@.to_multiset().count(x) == old_v.subrange(0, n as int).to_multiset().count(x));

    // rebuild v as pos ++ neg
    v.clear();

    let mut k: usize = 0;
    while k < pos.len()
        invariant k <= pos.len(),
        invariant v.len() == k,
        invariant forall|x: i32| #[trigger pos] v@.subrange(0, k as int).to_multiset().count(x) == pos@.subrange(0, k as int).to_multiset().count(x)
    {
        v.push(pos[k]);
        k += 1;
    }

    // after copying pos, v's multiset equals pos@
    assert(v.len() == pos.len());
    assert(forall|x: i32| #[trigger pos] v@.to_multiset().count(x) == pos@.to_multiset().count(x));

    let mut k2: usize = 0;
    while k2 < neg.len()
        invariant k2 <= neg.len(),
        invariant v.len() == pos.len() + k2,
        invariant forall|x: i32| #[trigger neg] v@.subrange(0, (pos.len() + k2) as int).to_multiset().count(x) == pos@.to_multiset().count(x) + neg@.subrange(0, k2 as int).to_multiset().count(x)
    {
        v.push(neg[k2]);
        k2 += 1;
    }

    // after copying neg, v's multiset equals pos@ + neg@
    assert(v.len() == pos.len() + neg.len());
    assert(forall|x: i32| #[trigger old_v] v@.to_multiset().count(x) == pos@.to_multiset().count(x) + neg@.to_multiset().count(x));

    let i: usize = pos.len();

    // show bounds
    assert(0 <= i && i <= v.len());

    // show positives in prefix
    assert(forall|u: int| 0 <= u && u < i as int ==> v@[u] >= 0);
    assert(positive(v@.subrange(0, i as int)));

    // show negatives in suffix
    assert(forall|u: usize| i <= u && u < v.len() ==> v[u as int] < 0);
    assert(strict_negative(v, i, v.len()));

    // show permutation: counts equal for all x
    // From earlier, pos@ + neg@ equals old_v.subrange(0,n) which is old_v
    assert(forall|x: i32| #[trigger old_v] v@.to_multiset().count(x) == old_v.to_multiset().count(x));

    i
}
// </vc-code>

fn main() {}

}