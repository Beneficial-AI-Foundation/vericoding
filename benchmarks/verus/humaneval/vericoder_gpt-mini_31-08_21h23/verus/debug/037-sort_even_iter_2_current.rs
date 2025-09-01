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

// Lemma: swapping two indices in a sequence preserves counts (for i32)
proof fn lemma_swap_counts_i32(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len()
    requires 0 <= j < s.len()
    ensures forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    if i == j {
        // swapping the same index leaves sequence unchanged
        forall|x: i32| {
            assert(s.update(i, s[j]).update(j, s[i]) == s);
            assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
        }
    } else {
        let a = s[i];
        let b = s[j];
        // consider arbitrary x
        forall|x: i32| {
            // apply lemma for single update at i -> b
            assert(inner_expr_lemma_update_effect_on_count(s, i, b, x));
            // apply lemma for update at j on s1
            let s1 = s.update(i, b);
            assert(inner_expr_lemma_update_effect_on_count(s1, j, a, x));
            if a == b {
                // if equal, both updates do not change sequence
                assert(count(s1.update(j, a), x) == count(s, x));
            } else {
                if x == a {
                    // case x equals a (and a != b)
                    // compute count(s1, x)
                    // From first lemma: since b != x and a == x, count(s1,x) = count(s,x) - 1
                    // From second lemma: since a == x and s1[j] == b != x, count(s2,x) = count(s1,x) + 1 = count(s,x)
                    assert(b != x);
                    assert(a == x);
                    // instantiate first lemma result
                    assert(count(s1, x) == count(s, x) - 1);
                    // instantiate second lemma result
                    assert(count(s1.update(j, a), x) == count(s1, x) + 1);
                    assert(count(s1.update(j, a), x) == count(s, x));
                } else if x == b {
                    // case x equals b (and a != b)
                    // From first lemma: since b == x and a != x
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

// Lemma: swapping two indices in a sequence preserves counts (for i32)
proof fn lemma_swap_counts_i32(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len()
    requires 0 <= j < s.len()
    ensures forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    if i == j {
        // swapping the same index leaves sequence unchanged
        forall|x: i32| {
            assert(s.update(i, s[j]).update(j, s[i]) == s);
            assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
        }
    } else {
        let a = s[i];
        let b = s[j];
        // consider arbitrary x
        forall|x: i32| {
            // apply lemma for single update at i -> b
            assert(inner_expr_lemma_update_effect_on_count(s, i, b, x));
            // apply lemma for update at j on s1
            let s1 = s.update(i, b);
            assert(inner_expr_lemma_update_effect_on_count(s1, j, a, x));
            if a == b {
                // if equal, both updates do not change sequence
                assert(count(s1.update(j, a), x) == count(s, x));
            } else {
                if x == a {
                    // case x equals a (and a != b)
                    // compute count(s1, x)
                    // From first lemma: since b != x and a == x, count(s1,x) = count(s,x) - 1
                    // From second lemma: since a == x and s1[j] == b != x, count(s2,x) = count(s1,x) + 1 = count(s,x)
                    assert(b != x);
                    assert(a == x);
                    // instantiate first lemma result
                    assert(count(s1, x) == count(s, x) - 1);
                    // instantiate second lemma result
                    assert(count(s1.update(j, a), x) == count(s1, x) + 1);
                    assert(count(s1.update(j, a), x) == count(s, x));
                } else if x == b {
                    // case x equals b (and a != b)
                    // From first lemma: since b == x and a != x
// </vc-code>

fn main() {}
}