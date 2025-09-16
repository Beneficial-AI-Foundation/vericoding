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
    /* code modified by LLM (iteration 5): Fix syntax error - proper chained comparison */
    let mut result = l;
    let n = result.len();
    
    if n == 0 {
        return result;
    }
    
    let mut i: usize = 0;
    while i < n
        invariant
            n == result.len(),
            n == l.len(),
            0 <= i <= n,
            permutes(result@, l@),
            forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
            forall|p: int, q: int| 0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
            forall|p: int, q: int| 0 <= p < i && i <= q < n && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
    {
        if i % 2 == 0 {
            let mut j: usize = i + 2;
            while j < n
                invariant
                    n == result.len(),
                    n == l.len(),
                    i < n,
                    i % 2 == 0,
                    i + 2 <= j <= n,
                    permutes(result@, l@),
                    forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
                    forall|p: int, q: int| 0 <= p < q < i && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
                    forall|p: int, q: int| 0 <= p < i && i <= q < n && p % 2 == 0 && q % 2 == 0 ==> result[p] <= result[q],
                    forall|k: int| i as int < k && k < j && k % 2 == 0 ==> result[i as int] <= result[k],
            {
                if j % 2 == 0 && result[j] < result[i] {
                    proof {
                        lemma_permutes_update(result@, result@, i as int, j as int);
                    }
                    let temp = result[i];
                    result.set(i, result[j]);
                    result.set(j, temp);
                }
                j = j + 1;
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}