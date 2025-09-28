use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
spec fn exists_even_in_seq(s: Seq<int>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_even(s[i])
}

proof fn lemma_exists_even_implies_product_even(s: Seq<int>)
    ensures
        exists_even_in_seq(s) ==> exists|i: int| 0 <= i < s.len() && is_even(s[i]),
{
}

proof fn lemma_product_even_implies_exists_even(s: Seq<int>)
    ensures
        (exists|i: int| 0 <= i < s.len() && is_even(s[i])) ==> exists_even_in_seq(s),
{
}

spec fn is_even_spec(n: int) -> bool {
    n % 2 == 0
}

proof fn lemma_is_even_equiv(n: int)
    ensures is_even(n) == is_even_spec(n),
{
}

proof fn lemma_seq_index_access(a: Seq<int>, i: usize)
    requires 0 <= i < a.len()
    ensures a[i] == a@[i as int]
{
}

proof fn lemma_forall_implies_not_exists(s: Seq<int>, i: int)
    requires 
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> !is_even(s[j])
    ensures 
        !exists_even_in_seq(s.subrange(0, i as usize))
{
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let n = a.len();
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < (i as int) ==> !is_even(a@[j]),
            exists_even_in_seq(a@) == exists|j: int| (i as int) <= j < (n as int) && is_even(a@[j]),
    {
        proof { lemma_seq_index_access(a@, i); }
        if is_even(a[i]) {
            proof { lemma_exists_even_implies_product_even(a@); }
            return true;
        }
        proof { lemma_forall_implies_not_exists(a@, i as int); }
        i += 1;
    }
    proof { lemma_product_even_implies_exists_even(a@); }
    false
}
// </vc-code>

fn main() {
}

}