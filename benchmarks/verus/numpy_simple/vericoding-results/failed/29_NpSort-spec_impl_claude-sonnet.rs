// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn multiset_count<T>(s: Seq<T>, x: T) -> nat {
    s.filter(|y| y == x).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch in lemma call */
fn lemma_multiset_count_preserved_by_swap<T>(s: Seq<T>, i: nat, j: nat, x: T)
    requires
        i < s.len(),
        j < s.len(),
    ensures
        multiset_count(s.update(i as int, s[j as int]).update(j as int, s[i as int]), x) == multiset_count(s, x),
{
    proof {
        let s1 = s.update(i as int, s[j as int]);
        let s2 = s1.update(j as int, s[i as int]);
        
        if i == j {
            assert(s2 =~= s);
        } else {
            assert(forall|k: int| 0 <= k < s.len() ==> {
                if k == i {
                    s2[k] == s[j as int]
                } else if k == j {
                    s2[k] == s[i as int]
                } else {
                    s2[k] == s[k]
                }
            });
            
            assert(s2.filter(|y| y == x).len() == s.filter(|y| y == x).len());
        }
    }
}

fn lemma_multiset_count_unchanged<T>(s: Seq<T>, i: nat, val: T, x: T)
    requires
        i < s.len(),
        s[i as int] == val,
    ensures
        multiset_count(s.update(i as int, val), x) == multiset_count(s, x),
{
    proof {
        let s_new = s.update(i as int, val);
        assert(forall|k: int| 0 <= k < s.len() ==> {
            if k == i {
                s_new[k] == val && s[k] == val
            } else {
                s_new[k] == s[k]
            }
        });
        assert(s_new.filter(|y| y == x).len() == s.filter(|y| y == x).len());
    }
}

spec fn is_sorted(s: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] as int <= s[j] as int
}
// </vc-helpers>

// <vc-spec>
fn sort(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
        forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatch in lemma call */
    let mut result = a;
    let n = result.len();
    
    let mut i = 1;
    while i < n
        invariant
            result.len() == a.len(),
            1 <= i <= n,
            n == a.len(),
            forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i ==> result[k1] as int <= result[k2] as int,
        decreases n - i
    {
        let mut j = i;
        while j > 0 && j < result.len() && j - 1 < result.len() && result[j - 1] > result[j]
            invariant
                0 <= j <= i,
                i < n,
                result.len() == a.len(),
                j < result.len(),
                forall|x: i8| multiset_count(result@, x) == multiset_count(a@, x),
                forall|k1: int, k2: int| 0 <= k1 < k2 <= i ==> {
                    if k2 <= j || k1 >= j {
                        result[k1] as int <= result[k2] as int
                    } else {
                        true
                    }
                },
            decreases j
        {
            proof {
                lemma_multiset_count_preserved_by_swap(result@, (j - 1) as nat, j as nat, result[j] as i8);
            }
            let temp = result[j];
            result.set(j, result[j - 1]);
            result.set(j - 1, temp);
            j = j - 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}