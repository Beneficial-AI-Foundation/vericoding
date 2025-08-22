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

spec fn permutes<T>(s1: Seq<T>, s2: Seq<T>) -> (result:bool) {
    forall|x: T| count(s1, x) == count(s2, x)
}
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

proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    // pre-conditions-start
    requires
        0 <= i < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_lemma_update_effect_on_count(s, i, v, x),
    decreases s.len(),
    // post-conditions-end
{
    assume(false);  // TODO: Remove this line and implement the proof
}
// pure-end

proof fn lemma_swapping_produces_a_permutation<T>(s: Seq<T>, i: int, j: int)
    // pre-conditions-start
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        permutes(s.update(i, s[j]).update(j, s[i]), s),
    // post-conditions-end
{
    assume(false);  // TODO: Remove this line and implement the proof
}
// pure-end

#[verifier::loop_isolation(false)]
fn sort_pred(l: Vec<i32>, p: Vec<bool>) -> (l_prime: Vec<i32>)
    // pre-conditions-start
    requires
        l.len() == p.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        l_prime.len() == l.len(),
        forall|i: int| 0 <= i < l.len() && !p[i] ==> l_prime[i] == l[i],
        forall|i: int, j: int|
            #![auto]
            0 <= i < j < l.len() && p[i] && p[j] ==> l_prime[i] <= l_prime[j],
        permutes(l_prime@, l@),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

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
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

}
fn main() {}
