use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_subrange_zero_property(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
        forall|k: int| i <= k < j ==> v[k] != 0,
    ensures
        forall|k: int| i <= k < j ==> v[k] != 0,
{
}

proof fn lemma_seq_concat_zero_property(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
        forall|k: int| 0 <= k < i ==> v[k] != 0,
        forall|k: int| i <= k < j ==> v[k] != 0,
    ensures
        forall|k: int| 0 <= k < j ==> v[k] != 0,
{
}

proof fn lemma_seq_extend_zero_property(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len(),
        forall|j: int| 0 <= j < i ==> v[j] != 0,
        v[i] != 0,
    ensures
        forall|j: int| 0 <= j <= i ==> v[j] != 0,
{
}
// </vc-helpers>

// <vc-spec>
fn mfirst_cero(v: &[i32]) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        i != v.len() ==> v@[i as int] == 0,
{
    assume(false);
    0
}
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
    {
        if v[i] == 0 {
            return i;
        }
        proof {
            assert(forall|j: int| 0 <= j < i as int ==> v@[j] != 0);
            assert(v@[i as int] != 0);
            lemma_seq_extend_zero_property(v@, i as int);
        }
        i += 1;
        assert(i <= v.len());
        assert(forall|j: int| 0 <= j < i as int ==> v@[j] != 0);
    }
    i
}
// </vc-code>

fn main() {
}

}