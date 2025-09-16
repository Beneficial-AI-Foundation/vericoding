// <vc-preamble>
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

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}

spec fn inner_expr_lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T) -> (result:bool) {
    count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed Seq::new call to include length argument */
spec fn extract_even<T>(s: Seq<T>) -> Seq<T> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        let first = s[0];
        let rest = s.skip(1);
        Seq::new(1, first) + extract_odd(rest)
    }
}

spec fn extract_odd<T>(s: Seq<T>) -> Seq<T> {
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest = s.skip(1);
        extract_even(rest)
    }
}

proof fn lemma_count_decomposition<T>(s: Seq<T>, x: T)
    ensures
        count(s, x) == count(extract_even(s), x) + count(extract_odd(s), x)
{
    if s.len() == 0 {
    } else {
        let first = s[0];
        let rest = s.skip(1);
        lemma_count_decomposition(rest, x);
    }
}

proof fn lemma_extract_odd_equal<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() && i % 2 == 1 ==> s1[i] == s2[i],
    ensures
        extract_odd(s1) == extract_odd(s2)
{
    if s1.len() == 0 {
    } else {
        let s1_rest = s1.skip(1);
        let s2_rest = s2.skip(1);
        lemma_extract_odd_equal(s1_rest, s2_rest);
    }
}

proof fn lemma_permutation_by_even_odd<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() && i % 2 == 1 ==> s1[i] == s2[i],
        permutes(extract_even(s1), extract_even(s2)),
    ensures
        permutes(s1, s2)
{
    lemma_extract_odd_equal(s1, s2);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn sort_even(l: Vec<i32>) -> (result: Vec<i32>)

    ensures
        l.len() == result.len(),
        permutes(result@, l@),
        forall|i: int| 0 <= i < l.len() && i % 2 == 1 ==> result[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && i % 2 == 0 && j % 2 == 0 ==> result[i] <= result[j],
// </vc-spec>
// <vc-code>
{
    let mut result = l.clone();
    let mut even_elems: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            even_elems.len() == (i + 1) / 2,
    {
        if i % 2 == 0 {
            even_elems.push(l[i]);
        }
        i += 1;
    }

    even_elems.sort();

    let mut idx = 0;
    let mut j = 0;
    while j < result.len()
        invariant
            0 <= j <= result.len(),
            0 <= idx <= even_elems.len(),
            idx == (j + 1) / 2,
    {
        if j % 2 == 0 {
            result[j] = even_elems[idx];
            idx += 1;
        }
        j += 1;
    }

    proof {
        assert(extract_even(result@) == even_elems@);
        assert(permutes(even_elems@, extract_even(l@)));
        lemma_permutation_by_even_odd(l@, result@);
    }

    result
}
// </vc-code>

}
fn main() {}