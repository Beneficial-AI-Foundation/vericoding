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
/* code modified by LLM (iteration 3): added decreases clauses to all while loops to fix compilation error */
{
    let mut result = l.clone();
    let mut evens: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < l.len()
        decreases l.len() - i
    {
        if i % 2 == 0 {
            evens.push(l[i]);
        }
        i += 1;
    }
    // Manual bubble sort on evens
    let mut k = 0;
    while k < evens.len()
        decreases evens.len() - k
    {
        let mut m = k + 1;
        while m < evens.len()
            decreases evens.len() - m
        {
            if evens[k] > evens[m] {
                let temp = evens[k];
                evens[k] = evens[m];
                evens[m] = temp;
            }
            m += 1;
        }
        k += 1;
    }
    let mut j = 0;
    i = 0;
    while i < l.len()
        decreases l.len() - i
    {
        if i % 2 == 0 {
            result[i] = evens[j];
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}