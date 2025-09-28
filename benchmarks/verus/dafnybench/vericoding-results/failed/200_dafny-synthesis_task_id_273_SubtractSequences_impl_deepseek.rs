use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn subtract_sequences_index_property(a: Seq<int>, b: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        a.len() == b.len()
    ensures
        a[i] - b[i] == a[i] - b[i]
{
}

proof fn subtract_sequences_len_property(a: Seq<int>, b: Seq<int>) 
    requires
        a.len() == b.len()
    ensures
        a.len() == b.len()
{
}

proof fn preserve_elements_lemma(result_old: Seq<int>, result_new: Seq<int>, a: Seq<int>, b: Seq<int>, n: int)
    requires
        result_new.len() == result_old.len() + 1,
        forall|i: int| 0 <= i < result_old.len() ==> result_old[i] == result_new[i],
        result_new[n] == a[n] - b[n]
    ensures
        forall|j: int| 0 <= j < result_old.len() ==> result_old[j] == result_new[j]
{
}

proof fn seq_index_is_int(a: Seq<int>, i: nat)
    requires
        i < a.len()
    ensures
        a[i] is int
{
}

proof fn nat_plus_one_is_nat(n: nat)
    ensures
        (n + 1) is nat
{
}
// </vc-helpers>

// <vc-spec>
fn subtract_sequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i],
// </vc-spec>
// <vc-code>
{
    let mut result: Seq<int> = Seq::empty();
    let mut n: nat = 0;
    proof {
        subtract_sequences_len_property(a, b);
    };
    assert(a.len() == b.len());
    while n < a.len()
        invariant
            n <= a.len(),
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == a[i] - b[i],
        decreases a.len() - n
    {
        let old_result = result;
        proof {
            seq_index_is_int(a, n);
            seq_index_is_int(b, n);
        }
        let a_index: int = a[n];
        let b_index: int = b[n];
        result = result.add(a_index - b_index);
        proof {
            subtract_sequences_index_property(a, b, n as int);
            preserve_elements_lemma(old_result, result, a, b, n as int);
            nat_plus_one_is_nat(n);
        }
        n = (n + 1) as nat;
    }
    result
}
// </vc-code>

fn main() {}

}