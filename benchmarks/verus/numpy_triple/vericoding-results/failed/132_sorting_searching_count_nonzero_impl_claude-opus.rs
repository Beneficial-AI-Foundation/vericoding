// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas to prove postconditions about count_nonzero_up_to */
spec fn count_nonzero_up_to(s: Seq<i32>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0int
    } else {
        count_nonzero_up_to(s, n - 1) + if s[n - 1] != 0 { 1int } else { 0int }
    }
}

proof fn lemma_all_zero(s: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] == 0,
    ensures
        count_nonzero_up_to(s, n) == 0,
    decreases n
{
    if n > 0 {
        lemma_all_zero(s, n - 1);
    }
}

proof fn lemma_all_nonzero(s: Seq<i32>, n: int)
    requires
        0 <= n <= s.len(),
        forall|i: int| 0 <= i < n ==> s[i] != 0,
    ensures
        count_nonzero_up_to(s, n) == n,
    decreases n
{
    if n > 0 {
        lemma_all_nonzero(s, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added proof statements to establish postconditions */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count <= i,
            count == count_nonzero_up_to(a@, i as int),
        decreases a.len() - i
    {
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(count == count_nonzero_up_to(a@, a.len() as int));
        
        if forall|j: int| 0 <= j < a.len() ==> a[j] == 0 {
            lemma_all_zero(a@, a.len() as int);
            assert(count == 0);
        }
        
        if forall|j: int| 0 <= j < a.len() ==> a[j] != 0 {
            lemma_all_nonzero(a@, a.len() as int);
            assert(count == a.len());
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}