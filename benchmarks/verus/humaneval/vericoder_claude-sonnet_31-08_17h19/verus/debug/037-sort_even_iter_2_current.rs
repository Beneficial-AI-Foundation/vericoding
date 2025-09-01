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
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures inner_expr_lemma_update_effect_on_count(s, i, v, x)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.update(i, v) =~= seq![v]);
        assert(count(s.update(i, v), x) == if v == x { 1int } else { 0int });
        assert(count(s, x) == if s[0] == x { 1int } else { 0int });
    } else {
        if i == 0 {
            assert(s.update(i, v) =~= seq![v] + s.skip(1));
            assert(count(s.update(i, v), x) == count(s.skip(1), x) + if v == x { 1int } else { 0int });
            assert(count(s, x) == count(s.skip(1), x) + if s[0] == x { 1int } else { 0int });
        } else {
            lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
            assert(s.update(i, v) =~= seq![s[0]] + s.skip(1).update(i - 1, v));
        }
    }
}

proof fn lemma_swap_preserves_count<T>(s: Seq<T>, i: int, j: int, x: T)
    requires 0 <= i < s.len(), 0 <= j < s.len()
    ensures count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    let s1 = s.update(i, s[j]);
    lemma_update_effect_on_count(s, i, s[j], x);
    lemma_update_effect_on_count(s1, j, s[i], x);
    
    if i == j {
        assert(s.update(i, s[j]).update(j, s[i]) =~= s);
    } else {
        assert(s1[j] == s[j]);
        assert(s1[i] == s[j]);
    }
}

proof fn lemma_swap_preserves_permutation<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i < s.len(), 0 <= j < s.len()
    ensures permutes(s.update(i, s[j]).update(j, s[i]), s)
{
    assert forall|x: T| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_swap_preserves_count(s, i, j, x);
    };
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
    let mut result = l.clone();
    let n = result.len();
    
    let mut i = 0;
    while i < n
        invariant
            result.len() == n,
            n == l.len(),
            permutes(result@, l@),
            forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
            forall|p: int, q: int|
                #![auto]
                0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
            forall|p: int, q: int|
                #![auto]
                0 <= p < i && p % 2 == 0 && i <= q < n && q % 2 == 0 ==> result[p] <= result[q],
    {
        if i % 2 == 0 {
            let mut min_idx = i;
            let mut j = i + 2;
            
            while j < n
                invariant
                    result.len() == n,
                    n == l.len(),
                    permutes(result@, l@),
                    forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
                    i <= min_idx < n,
                    min_idx % 2 == 0,
                    i <= j,
                    j % 2 == 0,
                    forall|k: int| i <= k < j && k % 2 == 0 ==> result@[min_idx as int] <= result@[k],
                    forall|p: int, q: int|
                        #![auto]
                        0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
                    forall|p: int, q: int|
                        #![auto]
                        0 <= p < i && p % 2 == 0 && i <= q < n && q % 2 == 0 ==> result[p] <= result[q],
            {
                if result[j] < result[min_idx] {
                    min_idx = j;
                }
                j += 2;
            }
            
            if min_idx != i {
                proof {
                    lemma_swap_preserves_permutation(result@, i as int, min_idx as int);
                }
                let temp = result[i];
                result.set(i, result[min_idx]);
                result.set(min_idx, temp);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}