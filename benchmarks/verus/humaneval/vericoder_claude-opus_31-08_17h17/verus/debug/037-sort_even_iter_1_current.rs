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
{
    assert(count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }) by {
        let s_updated = s.update(i, v);
        assert forall|j: int| 0 <= j < s.len() && j != i implies s_updated[j] == s[j];
        assert(s_updated[i] == v);
    }
}

proof fn lemma_permutation_update<T>(s1: Seq<T>, s2: Seq<T>, i: int, v: T)
    requires 
        0 <= i < s1.len(),
        s1.len() == s2.len(),
        permutes(s1, s2),
        s1[i] == s2[i]
    ensures permutes(s1.update(i, v), s2.update(i, v))
{
    assert forall|x: T| count(s1.update(i, v), x) == count(s2.update(i, v), x) by {
        lemma_update_effect_on_count(s1, i, v, x);
        lemma_update_effect_on_count(s2, i, v, x);
    }
}

proof fn lemma_count_swap<T>(s: Seq<T>, i: int, j: int, x: T)
    requires 0 <= i < s.len(), 0 <= j < s.len(), i != j
    ensures count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    let s1 = s.update(i, s[j]);
    let s2 = s1.update(j, s[i]);
    
    lemma_update_effect_on_count(s, i, s[j], x);
    lemma_update_effect_on_count(s1, j, s[i], x);
}

proof fn lemma_swap_preserves_permutation<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i < s.len(), 0 <= j < s.len(), i != j
    ensures permutes(s, s.update(i, s[j]).update(j, s[i]))
{
    assert forall|x: T| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x) by {
        lemma_count_swap(s, i, j, x);
    }
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
    
    if n == 0 {
        return result;
    }
    
    let mut i = 0;
    while i < n
        invariant
            n == result.len(),
            n == l.len(),
            permutes(result@, l@),
            forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
            forall|p: int, q: int| 
                0 <= p < q < n && p % 2 == 0 && q % 2 == 0 && q < i ==> 
                result[p] <= result[q],
            forall|p: int, q: int|
                0 <= p < i && p % 2 == 0 && i <= q < n && q % 2 == 0 ==>
                result[p] <= result[q],
            i <= n,
            i % 2 == 0 || i == n,
    {
        if i % 2 == 0 {
            let mut j = i + 2;
            let mut min_idx = i;
            
            while j < n
                invariant
                    n == result.len(),
                    n == l.len(),
                    permutes(result@, l@),
                    forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
                    forall|p: int, q: int| 
                        0 <= p < q < n && p % 2 == 0 && q % 2 == 0 && q < i ==> 
                        result[p] <= result[q],
                    forall|p: int, q: int|
                        0 <= p < i && p % 2 == 0 && i <= q < n && q % 2 == 0 ==>
                        result[p] <= result[q],
                    i < n,
                    i % 2 == 0,
                    j <= n + 1,
                    min_idx % 2 == 0,
                    i <= min_idx < n,
                    forall|k: int| i <= k < j && k % 2 == 0 ==> result[min_idx] <= result[k],
            {
                if j < n && j % 2 == 0 && result[j] < result[min_idx] {
                    min_idx = j;
                }
                j = j + 2;
            }
            
            if min_idx != i {
                let temp = result[i];
                result.set(i, result[min_idx]);
                
                proof {
                    lemma_update_effect_on_count(result@, i, result@[min_idx], temp);
                }
                
                result.set(min_idx, temp);
                
                proof {
                    lemma_swap_preserves_permutation(l@, i as int, min_idx as int);
                }
            }
        }
        
        i = i + 2;
    }
    
    result
}
// </vc-code>

fn main() {}
}