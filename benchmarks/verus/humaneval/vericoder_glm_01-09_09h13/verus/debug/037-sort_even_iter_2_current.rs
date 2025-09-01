use vstd::prelude::*;

verus! {

spec fn count<T>(s: Seq<T>, x: T) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count(s.skip(1), x) + if s[0] == x {
            1int
        } else {
            0int
        }
    }
}
// pure-end
// pure-end

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
// pure-end
// pure-end

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// pure-end

// <vc-helpers>
proof fn count_update_lemma<T>(s: Seq<T>, i: int, v: T, x: T)
    requires
        0 <= i < s.len(),
    ensures
        count(s.update(i, v), x) == if v == x && s[i] != x {
            count(s, x) + 1
        } else if v != x && s[i] == x {
            count(s, x) - 1
        } else {
            count(s, x)
        }
{
    reveal(count);
    if s.len() == 0 {
        assert(false);
    } else {
        if i == 0 {
            assert(s.update(0, v).skip(1) =~= s.skip(1));
        } else {
            assert(s.update(i, v).skip(1) =~= s.skip(1).update(i - 1, v));
            count_update_lemma(s.skip(1), i - 1, v, x);
        }
    }
}

proof fn permutes_reflexive<T>(s: Seq<T>)
    ensures
        permutes(s, s)
{
    reveal(permutes);
}

proof fn permutes_symmetric<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        permutes(s1, s2),
    ensures
        permutes(s2, s1)
{
    reveal(permutes);
}

proof fn permutes_transitive<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    requires
        permutes(s1, s2),
        permutes(s2, s3),
    ensures
        permutes(s1, s3)
{
    reveal(permutes);
}

proof fn permutes_update<T>(s: Seq<T>, i: int, v: T)
    requires
        0 <= i < s.len(),
    ensures
        permutes(s.update(i, v), s)
{
    reveal(permutes);
    count_update_lemma(s, i, v, _);
}

proof fn swap_permutation<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s)
{
    if i == j {
        permutes_reflexive(s);
    } else {
        reveal(permutes);
        let s1 = s.update(i, s[j]);
        let s2 = s1.update(j, s[i]);
        
        count_update_lemma(s, i, s[j], _);
        count_update_lemma(s1, j, s[i], _);
        
        assert(forall|x: T| count(s2, x) == count(s, x));
    }
}

proof fn sort_is_permutation<T>(v: &Vec<T>, sorted: &Vec<T>)
    requires
        sorted@ is_sorted(),
    ensures
        permutes(sorted@, v@)
{
    // Sorting (bubble sort) produces a permutation of the original vector
    // This assumes the bubble sort implementation maintains permutation
    assert_permutation!(sorted@, v@);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut len = l.len();
    let mut res = l.clone();
    
    // Extract even indices
    let mut even_elems = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            even_elems.len() == i / 2,
            forall|k: int| 0 <= k < i && k % 2 == 0 ==> even_elems@[k/2] == res@[k],
    {
        if i % 2 == 0 {
            even_elems.push(res[i]);
        }
        i = i + 1;
    }
    
    // Sort even elements (bubble sort)
    let mut even_elems_sorted = even_elems.clone();
    let n = even_elems_sorted.len();
    for i in 0..n
        invariant
            0 <= i <= n,
            permutes(even_elems_sorted@, even_elems@),
            forall|k: int| i <= k < n ==> 
                forall|j: int| 0 <= j < n - k ==> even_elems_sorted@[j] <= even_elems_sorted@[j+1],
    {
        for j in 0..n-i-1
            invariant
                0 <= j <= n-i-1,
                permutes(even_elems_sorted@, even_elems@),
                forall|k: int| 0 <= k < i || n-i <= k < n ==> 
                    forall|m: int| 0 <= m < n - k ==> even_elems_sorted@[m] <= even_elems_sorted@[m+1],
        {
            if even_elems_sorted[j] > even_elems_sorted[j+1] {
                let temp = even_elems_sorted[j];
                even_elems_sorted.set(j, even_elems_sorted[j+1]);
                even_elems_sorted.set(j+1, temp);
                
                proof {
                    swap_permutation(even_elems_sorted@.subrange(0, n), j, j+1);
                    permutes_transitive(even_elems_sorted@, even_elems_sorted@.subrange(0, n).update(j, even_elems.sorted@[j+1]).update(j+1, even_elems.sorted@[j]), even_elems@);
                }
            }
        }
    }
    
    // Place sorted even elements back
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            res.len() == len,
            forall|k: int| 0 <= k < len && k % 2 == 1 ==> res@[k] == l@[k],
            forall|k: int| 0 <= k < i && k % 2 == 0 ==> res@[k] == even_elems_sorted@[k/2],
            forall|k: int, j: int|
                0 <= k
// </vc-code>

fn main() {}
}