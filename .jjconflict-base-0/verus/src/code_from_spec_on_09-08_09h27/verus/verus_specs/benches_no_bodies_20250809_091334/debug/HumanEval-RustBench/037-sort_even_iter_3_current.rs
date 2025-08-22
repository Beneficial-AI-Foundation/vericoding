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
    let updated_s = s.update(i, v);
    
    if i == 0 {
        // Base case: updating the first element
        assert(updated_s[0] == v);
        assert(updated_s.skip(1) == s.skip(1));
        assert(count(updated_s.skip(1), x) == count(s.skip(1), x));
    } else {
        // Recursive case: updating element at position i > 0
        assert(updated_s[0] == s[0]);
        assert(updated_s.skip(1) == s.skip(1).update(i - 1, v));
        lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
    }
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
    let swapped = s.update(i, s[j]).update(j, s[i]);
    
    assert forall|x: T| count(swapped, x) == count(s, x) by {
        if i == j {
            assert(swapped == s);
        } else {
            lemma_update_effect_on_count(s, i, s[j], x);
            lemma_update_effect_on_count(s.update(i, s[j]), j, s[i], x);
            
            if x == s[i] && x == s[j] {
                // Both elements are x, no change in count
            } else if x == s[i] && x != s[j] {
                // We lose one x at position i and gain one x at position j
            } else if x != s[i] && x == s[j] {
                // We gain one x at position i and lose one x at position j
            } else {
                // Neither element is x, no change in count
            }
        }
    }
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
    let mut result = l.clone();
    let mut i: usize = 0;
    
    while i < result.len()
        invariant
            result.len() == l.len(),
            forall|k: int| 0 <= k < l.len() && !p[k] ==> result[k] == l[k],
            forall|k: int, j: int|
                #![auto]
                0 <= k < j < i && p[k] && p[j] ==> result[k] <= result[j],
            permutes(result@, l@),
    {
        if p[i] {
            let mut j: usize = i + 1;
            while j < result.len()
                invariant
                    i < result.len(),
                    i + 1 <= j <= result.len(),
                    result.len() == l.len(),
                    forall|k: int| 0 <= k < l.len() && !p[k] ==> result[k] == l[k],
                    forall|k: int, m: int|
                        #![auto]
                        0 <= k < m < i && p[k] && p[m] ==> result[k] <= result[m],
                    forall|k: int|
                        #![auto]
                        i < k < j && p[i as int] && p[k] ==> result[i as int] <= result[k],
                    permutes(result@, l@),
            {
                if p[j] && result[i] > result[j] {
                    proof {
                        lemma_swapping_produces_a_permutation(result@, i as int, j as int);
                    }
                    /* code modified by LLM (iteration 1): Fixed borrowing issue by storing values before mutation */
                    let val_i = result[i];
                    let val_j = result[j];
                    result.set(i, val_j);
                    result.set(j, val_i);
                }
                j += 1;
            }
        }
        i += 1;
    }
    
    result
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
    let mut p = Vec::new();
    let mut i: usize = 0;
    
    while i < l.len()
        invariant
            i <= l.len(),
            p.len() == i,
            forall|k: int| 0 <= k < i ==> p[k] == (k % 2 == 0),
    {
        p.push(i % 2 == 0);
        i += 1;
    }
    
    sort_pred(l, p)
}

}
fn main() {}