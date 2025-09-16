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
/* helper modified by LLM (iteration 5): fixed integer literal type inference */
proof fn lemma_update_effect_on_count<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len()
    ensures count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    }
    decreases s.len()
{
    if s.len() == 1 {
        // Base case: single element
        assert(i == 0);
        let updated = s.update(i, v);
        assert(updated.len() == 1);
        assert(updated[0] == v);
        // Count analysis for single element
        if v == x && s[i] != x {
            assert(count(updated, x) == 1int);
            assert(count(s, x) == 0int);
        } else if v != x && s[i] == x {
            assert(count(updated, x) == 0int);
            assert(count(s, x) == 1int);
        } else {
            assert(count(updated, x) == count(s, x));
        }
    } else {
        // Recursive case
        let updated = s.update(i, v);
        if i == 0 {
            assert(updated[0] == v);
            assert(updated.skip(1) =~= s.skip(1));
            assert(count(updated, x) == count(updated.skip(1), x) + if updated[0] == x { 1int } else { 0int });
            assert(count(s, x) == count(s.skip(1), x) + if s[0] == x { 1int } else { 0int });
        } else {
            assert(updated[0] == s[0]);
            assert(updated.skip(1) =~= s.skip(1).update(i - 1, v));
            lemma_update_effect_on_count(s.skip(1), i - 1, v, x);
        }
    }
}

proof fn lemma_swap_preserves_count<T>(s: Seq<T>, i: int, j: int, x: T)
    requires 0 <= i < s.len(), 0 <= j < s.len(), i != j
    ensures count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    let s1 = s.update(i, s[j]);
    let s2 = s1.update(j, s[i]);
    
    lemma_update_effect_on_count(s, i, s[j], x);
    lemma_update_effect_on_count(s1, j, s[i], x);
}

proof fn lemma_swap_permutes<T>(s: Seq<T>, i: int, j: int)
    requires 0 <= i < s.len(), 0 <= j < s.len(), i != j
    ensures permutes(s.update(i, s[j]).update(j, s[i]), s)
{
    let swapped = s.update(i, s[j]).update(j, s[i]);
    assert forall|x: T| count(swapped, x) == count(s, x) by {
        lemma_swap_preserves_count(s, i, j, x);
    }
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
/* code modified by LLM (iteration 5): fixed integer literal type inference */
{
    let mut result = l;
    let n = result.len();
    
    if n <= 2 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == n,
            n == l.len(),
            permutes(result@, l@),
            forall|k: int| 0 <= k < l.len() && k % 2 == 1 ==> result[k] == l[k],
            forall|k: int, m: int|
                #![auto]
                0 <= k < m < i && k % 2 == 0 && m % 2 == 0 ==> result[k] <= result[m],
            i <= n,
        decreases n - i
    {
        if i % 2 == 0 {
            let mut min_idx = i;
            let start_j = if i + 2 < n { i + 2 } else { n };
            let mut j = start_j;
            
            while j < n
                invariant
                    result.len() == n,
                    permutes(result@, l@),
                    forall|k: int| 0 <= k < l.len() && k % 2 == 1 ==> result[k] == l[k],
                    i <= min_idx < n,
                    min_idx % 2 == 0,
                    start_j <= j,
                    j <= n,
                    j % 2 == 0 || j == n,
                    forall|k: int| i <= k < j && k % 2 == 0 ==> result[min_idx as int] <= result[k],
                decreases n - j
            {
                if result[j] < result[min_idx] {
                    min_idx = j;
                }
                if j + 2 < n {
                    j += 2;
                } else {
                    break;
                }
            }
            
            if min_idx != i {
                proof {
                    lemma_swap_permutes(result@, i as int, min_idx as int);
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

}
fn main() {}