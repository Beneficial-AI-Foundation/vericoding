// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type annotations for sequence creation */
fn create_identity_seq(n: nat) -> Seq<nat>
    ensures
        create_identity_seq(n).len() == n,
        forall|i: int| 0 <= i < n as int ==> #[trigger] create_identity_seq(n)[i] == i as nat,
{
    if n == 0 {
        Seq::empty()
    } else {
        let mut seq = create_identity_seq((n - 1) as nat);
        seq = seq.push(n - 1);
        seq
    }
}
// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i8>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type errors in sequence indexing and old function usage */
    let n = a.len();
    let mut result: Vec<usize> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == j as nat,
        decreases n - i
    {
        result.push(i);
        i = i + 1;
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == n,
            result@.to_multiset() == create_identity_seq(n as nat).to_multiset(),
            forall|j: int, k: int| n - i <= j < k < n ==> 
                (a[result@[j] as int] < a[result@[k] as int] || 
                 (a[result@[j] as int] == a[result@[k] as int] && result@[j] < result@[k])),
            forall|j: int, k: int| 0 <= j < n-i && n-i <= k < n ==> 
                a[result@[j] as int] <= a[result@[k] as int],
        decreases n - i
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                0 <= j <= n - i - 1,
                result@.to_multiset() == create_identity_seq(n as nat).to_multiset(),
                forall|k: int| n-i <= k < n ==> result@[k as nat] == old(result)@[k as nat],
            decreases n - i - 1 - j
        {
            if a[result[j]] > a[result[j+1]] || (a[result[j]] == a[result[j+1]] && result[j] > result[j+1]) {
                let temp = result[j];
                result.set(j, result[j+1]);
                result.set(j+1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}