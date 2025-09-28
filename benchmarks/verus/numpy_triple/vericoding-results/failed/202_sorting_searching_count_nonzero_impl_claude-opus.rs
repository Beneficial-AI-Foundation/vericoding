// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas to establish postconditions */
spec fn count_nonzero_up_to(a: Seq<i8>, n: int) -> nat
    decreases n
{
    if n <= 0 {
        0
    } else {
        count_nonzero_up_to(a, n - 1) + if a[n - 1] != 0 { 1 } else { 0 }
    }
}

proof fn lemma_all_zeros(a: Seq<i8>, n: int)
    requires
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] == 0,
    ensures
        count_nonzero_up_to(a, n) == 0,
    decreases n
{
    if n > 0 {
        lemma_all_zeros(a, n - 1);
    }
}

proof fn lemma_all_nonzeros(a: Seq<i8>, n: int)
    requires
        0 <= n <= a.len(),
        forall|i: int| 0 <= i < n ==> a[i] != 0,
    ensures
        count_nonzero_up_to(a, n) == n,
    decreases n
{
    if n > 0 {
        lemma_all_nonzeros(a, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i8>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a@.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a@.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invariant and added proof lemmas */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count <= i,
            count as int == count_nonzero_up_to(a@, i as int),
        decreases a.len() - i
    {
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(count as int == count_nonzero_up_to(a@, a.len() as int));
        
        if forall|j: int| 0 <= j < a@.len() ==> a[j] == 0 {
            lemma_all_zeros(a@, a.len() as int);
            assert(count_nonzero_up_to(a@, a.len() as int) == 0);
        }
        
        if forall|j: int| 0 <= j < a@.len() ==> a[j] != 0 {
            lemma_all_nonzeros(a@, a.len() as int);
            assert(count_nonzero_up_to(a@, a.len() as int) == a.len() as int);
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}