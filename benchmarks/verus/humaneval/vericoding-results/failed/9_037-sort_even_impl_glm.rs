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
proof fn lemma_count_update<T>(s: Seq<T>, i: int, v: T, x: T)
    requires 0 <= i < s.len(),
    ensures count(s.update(i, v), x) == if v == x && s[i] != x {
        count(s, x) + 1
    } else if v != x && s[i] == x {
        count(s, x) - 1
    } else {
        count(s, x)
    },
{
    if s.len() == 0 {
        assert(s.update(i, v).len() == 0);
    } else {
        if i == 0 {
            lemma_count_update(s.skip(1), i - 1, v, x);
        } else {
            lemma_count_update(s.skip(1), i - 1, v, x);
        }
    }
}

proof fn lemma_permutes_reflexive<T>(s: Seq<T>)
    ensures permutes(s, s),
{
    assert(forall|x: T| count(s, x) == count(s, x));
}

proof fn lemma_permutes_symmetric<T>(s1: Seq<T>, s2: Seq<T>)
    requires permutes(s1, s2),
    ensures permutes(s2, s1),
{
    assert(forall|x: T| count(s2, x) == count(s1, x));
}

proof fn lemma_permutes_transitive<T>(s1: Seq<T>, s2: Seq<T>, s3: Seq<T>)
    requires permutes(s1, s2),
    requires permutes(s2, s3),
    ensures permutes(s1, s3),
{
    assert(forall|x: T| count(s1, x) == count(s3, x));
}

proof fn lemma_permutes_update<T>(s: Seq<T>, i: int, v: T)
    requires 0 <= i < s.len(),
    ensures permutes(s.update(i, v), s.update(i, v)),
{
    lemma_permutes_reflexive(s.update(i, v));
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
    let mut result = l;
    let n = result.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == n,
            permutes(result@, l@),
            forall|k: int| 0 <= k < n && k % 2 == 1 ==> result[k] == l[k],
            forall|k: int, j: int|
                0 <= k < j < i && k % 2 == 0 && j % 2 == 0 ==> result[k] <= result[j],
        decreases n - i,
    {
        if i % 2 == 0 {
            let mut j = i;
            let mut min_idx = i;
            
            while j < n
                invariant
                    i <= j <= n,
                    i <= min_idx < n,
                    min_idx % 2 == 0,
                    forall|k: int| i <= k < j && k % 2 == 0 ==> result[min_idx] <= result[k],
                decreases n - j,
            {
                if j % 2 == 0 && result[j] < result[min_idx] {
                    min_idx = j;
                }
                j = j + 1;
            }
            
            if min_idx != i {
                let temp = result[i];
                result[i] = result[min_idx];
                result[min_idx] = temp;
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}