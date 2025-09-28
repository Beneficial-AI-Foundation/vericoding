use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn add_lists_lemma(a: Seq<int>, b: Seq<int>, i: int)
    requires
        0 <= i <= a.len(),
        a.len() == b.len(),
    ensures
        forall|j: int| 0 <= j < i ==> (a + b)[j] == a[j] + b[j]
    decreases a.len() - i
{
    if i > 0 {
        add_lists_lemma(a, b, i - 1);
    }
}

spec fn seq_nat_index(seq: Seq<int>, idx: nat) -> int
    recommends idx < seq.len()
{
    seq[idx as int]
}
// </vc-helpers>

// <vc-spec>
fn add_lists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<int>::empty();
    let mut idx: nat = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|j: nat| j < idx ==> result[j] == seq_nat_index(a, j) + seq_nat_index(b, j),
    {
        proof {
            assert(idx < a.len());
        }
        let idx_int = idx as int;
        let a_val = a[idx_int];
        let b_val = b[idx_int];
        result = result.push(a_val + b_val);
        idx = idx + 1;
    }
    proof {
        add_lists_lemma(a, b, a.len() as int);
    }
    assert(result.len() == a.len());
    result
}
// </vc-code>

fn main() {}

}