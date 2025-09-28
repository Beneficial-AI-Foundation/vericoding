use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
fn seq_to_vec_implies_positive(s: Seq<int>, v: &Vec<int>) -> (b: bool)
    requires s == v@
    ensures b == positive(s) ==> ({
        let mut i: usize = 0;
        let mut result: bool = true;
        while i < v.len()
            invariant
                0 <= i as int <= v.len() as int,
                result == forall|j: int| 0 <= j < i as int ==> v@[j] >= 0,
                positive(s) ==> result,
        {
            if v[i] < 0 {
                result = false;
            }
            i = i + 1;
        }
        result
    })
{
    let mut i: usize = 0;
    let mut result: bool = true;
    while i < v.len()
        invariant
            0 <= i as int <= v.len() as int,
            result == forall|j: int| 0 <= j < i as int ==> v@[j] >= 0,
            positive(s) ==> result,
    {
        if v[i] < 0 {
            result = false;
        }
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut result: bool = true;
    while i < v.len()
        invariant
            0 <= i as int <= v.len() as int,
            result == forall|j: int| 0 <= j < i as int ==> v@[j] >= 0,
            result == positive(v@.subsequence(0, i as int)),
            positive(v@) ==> result,
    {
        if v[i] < 0 {
            result = false;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}