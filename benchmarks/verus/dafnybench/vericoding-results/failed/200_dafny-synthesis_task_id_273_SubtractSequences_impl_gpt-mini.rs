use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
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
    let mut v: Vec<int> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int
        invariant 0 <= i && i <= a.len() as int;
        invariant v.len() as int == i;
        invariant forall |j: int| 0 <= j && j < i ==> v@[j] == a[j] - b[j];
        decreases a.len() as int - i;
    {
        v.push(a[i] - b[i]);
        i += 1;
    }
    proof {
        // From the invariants and the loop exit condition, derive final equalities.
        assert(v.len() as int == i);
        assert(!(i < a.len() as int));
        assert(i <= a.len() as int);
        assert(i == a.len() as int);
        assert(v.len() as int == a.len() as int);
    }
    let result = v.into_seq();
    proof {
        // result.len() == a.len()
        assert(result.len() == a.len());
        // element-wise equality follows from the loop invariant at termination
        assert(forall |j: int| 0 <= j && j < result.len() ==> result[j] == a[j] - b[j]);
    }
    result
}
// </vc-code>

fn main() {}

}