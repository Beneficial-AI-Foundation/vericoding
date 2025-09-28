use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn subtract_sequences_spec(a: Seq<int>, b: Seq<int>, len: nat) -> Seq<int>
    recommends a.len() == b.len(), len <= a.len()
{
    Seq::<int>::new(len, |i: int| a[i] - b[i])
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
    let result = Seq::<int>::new(a.len() as nat, |i: int| a[i] - b[i]);
    
    proof {
        assert forall|i: int| 0 <= i < result.len() implies #[trigger] result[i] == a[i] - b[i] by {
            assert(0 <= i < a.len());
            assert(0 <= i < b.len());
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}