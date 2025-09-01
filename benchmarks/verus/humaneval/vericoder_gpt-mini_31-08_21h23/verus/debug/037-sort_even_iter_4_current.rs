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
spec fn seq_even(s: Seq<i32>) -> Seq<i32> {
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() == 1 {
        Seq::unit(s[0])
    } else {
        Seq::cons(s[0], seq_even(s.skip(2)))
    }
}

spec fn count_even_prefix(s: Seq<i32>, i: int, x: i32) -> int {
    if i == 0 {
        0
    } else {
        let prev = count_even_prefix(s, i - 1, x);
        prev + if (i - 1) % 2 == 0 && s[i - 1] == x { 1 } else { 0 }
    }
}

// Prove the effect of a single update on count for arbitrary sequences
proof fn inner_expr_update_count_proof<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
{
    if
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
spec fn seq_even(s: Seq<i32>) -> Seq<i32> {
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() == 1 {
        Seq::unit(s[0])
    } else {
        Seq::cons(s[0], seq_even(s.skip(2)))
    }
}

spec fn count_even_prefix(s: Seq<i32>, i: int, x: i32) -> int {
    if i == 0 {
        0
    } else {
        let prev = count_even_prefix(s, i - 1, x);
        prev + if (i - 1) % 2 == 0 && s[i - 1] == x { 1 } else { 0 }
    }
}

// Prove the effect of a single update on count for arbitrary sequences
proof fn inner_expr_update_count_proof<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
{
    if
// </vc-code>

fn main() {}
}