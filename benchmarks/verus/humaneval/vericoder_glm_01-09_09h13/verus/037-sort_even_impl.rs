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

proof fn permutes_even_odd<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() && i % 2 == 1 ==> s1[i] == s2[i],
        permutes(s1.subsequence(|i: int| i % 2 == 0), s2.subsequence(|i: int| i % 2 == 0)),
    ensures
        permutes(s1, s2)
{
    reveal(permutes);
    assert(forall|x: T| count(s1, x) == count(s2, x));
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
            forall|k: int|
                0 <= k < even_elems.len() ==> even_elems@[k] == l@[2 * k],
    {
        if i % 2 == 0 {
            even_elems.push(l[i]);
        }
        i = i + 1;
    }
    
    // Sort the even elements
    even_elems.sort();
    
    // Reconstruct the result
    let mut j = 0;
    i = 0;
    while i < len
        invariant
            0 <= i <= len,
            0 <= j <= even_elems.len(),
            j == i / 2,
            forall|k: int|
                0 <= k < i && k % 2 == 0 ==> res@[k] == even_elems@[k / 2],
            forall|k: int|
                0 <= k < i && k % 2 == 1 ==> res@[k] == l@[k],
    {
        if i % 2 == 0 {
            res.set(i, even_elems[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    
    res
}
// </vc-code>

fn main() {}
}