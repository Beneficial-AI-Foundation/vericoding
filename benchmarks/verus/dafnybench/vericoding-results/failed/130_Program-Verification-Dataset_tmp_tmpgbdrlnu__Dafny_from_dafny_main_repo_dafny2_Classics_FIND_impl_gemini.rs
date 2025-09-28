// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial(sub(n, 1)) }
}
// </vc-preamble>

// <vc-helpers>
spec fn is_permutation(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}

spec fn partitioned_prefix(s: Seq<i32>, i: int, f: int, n: int) -> bool {
    forall|p: int, q: int| 0 <= p < i && f <= q < n ==> s[p] <= s[q]
}

spec fn current_le_rhs_prefix(s: Seq<i32>, i: int, j: int, f: int) -> bool {
    forall|q: int| f <= q < j ==> s[i] <= s[q]
}
// </vc-helpers>

// <vc-spec>
fn find(A: &mut Vec<i32>, N: usize, f: usize)
    requires 
        old(A)@.len() == N,
        f < N,
    ensures
        forall|p: int, q: int| 0 <= p <= f as int <= q < N as int ==> A@[p] <= A@[q],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed decreases clause and permutation invariant */
    let ghost A_initial = A@;
    let mut i: usize = 0;
    while i <= f
        invariant
            0 <= i <= f + 1,
            f < N,
            A@.len() == N,
            is_permutation(A@, A_initial),
            partitioned_prefix(A@, i as int, f as int, N as int),
        decreases (f + 1) - i
    {
        let mut j: usize = f;
        while j < N
            invariant
                i <= f,
                f <= j <= N,
                f < N,
                A@.len() == N,
                is_permutation(A@, A_initial),
                partitioned_prefix(A@, i as int, f as int, N as int),
                current_le_rhs_prefix(A@, i as int, j as int, f as int),
            decreases N - j
        {
            if A[i] > A[j] {
                let ghost A_before_swap = A@;
                let temp = A[i];
                A.set(i, A[j]);
                A.set(j, temp);
                assert(A@.to_multiset() == A_before_swap.to_multiset());
            }
            j = j + 1;
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}