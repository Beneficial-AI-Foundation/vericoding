use vstd::prelude::*;

verus! {

// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// A version of Turing's additive factorial program [Dr. A. Turing, "Checking a large routine",
// In "Report of a Conference of High Speed Automatic Calculating Machines", pp. 67-69, 1949].

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial(sub(n, 1)) }
}


// Hoare's FIND program [C.A.R. Hoare, "Proof of a program: FIND", CACM 14(1): 39-45, 1971].
// The proof annotations here are not the same as in Hoare's article.

// In Hoare's words:
//   This program operates on an array A[1:N], and a value of f (1 <= f <= N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q (1 <= p <= f <= q <= N ==> A[p] <= A[f] <= A[q]).
//
// Here, we use 0-based indices, so we would say:
//   This method operates on an array A[0..N], and a value of f (0 <= f < N).
//   Its effect is to rearrange the elements of A in such a way that:
//     forall p,q :: 0 <= p <= f <= q < N ==> A[p] <= A[f] <= A[q]).

// <vc-helpers>
predicate sorted_around_f(a: Seq<i32>, f: int, n: int) {
    forall|p: int, q: int| 0 <= p <= f <= q < n ==> a[p] <= a[q]
}

predicate multiset_preserved(old_a: Seq<i32>, new_a: Seq<i32>) {
    old_a.to_multiset() == new_a.to_multiset()
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find(A: &mut Vec<i32>, N: usize, f: usize)
    requires 
        old(A)@.len() == N,
        f < N,
    ensures
        forall|p: int, q: int| 0 <= p <= f as int <= q < N as int ==> A@[p] <= A@[q],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if N <= 1 {
        return;
    }
    
    let mut i = 0;
    let mut j = N - 1;
    
    while i < j
        invariant
            0 <= i <= j < N,
            f < N,
            A.len() == N,
            multiset_preserved(old(A)@, A@),
            forall|p: int, q: int| 0 <= p < i && j < q < N as int ==> A@[p] <= A@[q],
            forall|p: int| 0 <= p < i ==> (f as int >= i ==> A@[p] <= A@[f]),
            forall|q: int| j < q < N as int ==> (f as int <= j ==> A@[f] <= A@[q])
        decreases j - i
    {
        if A[i] <= A[j] {
            if i == f {
                i += 1;
            } else if j == f {
                if j > 0 {
                    j -= 1;
                }
            } else {
                i += 1;
            }
        } else {
            let temp = A[i];
            A.set(i, A[j]);
            A.set(j, temp);
            
            if i == f {
                i += 1;
            } else if j == f {
                if j > 0 {
                    j -= 1;
                }
            } else {
                i += 1;
            }
        }
    }
}
// </vc-code>

fn main() {}

}