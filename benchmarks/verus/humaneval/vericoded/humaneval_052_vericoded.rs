// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn below_threshold(l: Seq<int>, t: int) -> bool {
    forall|i: int| 0 <= i < l.len() ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn check_below_threshold(l: Vec<i8>, t: i8) -> (result: bool)
    ensures result == below_threshold(l@.map(|_i: int, x: i8| x as int), t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof block to establish connection between mapped sequence and original sequence */
    let mut i = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            forall|j: int| 0 <= j < i ==> l@[j] < t as int,
        decreases l.len() - i
    {
        if l[i] >= t {
            proof {
                let mapped_seq = l@.map(|_k: int, x: i8| x as int);
                assert(mapped_seq[i as int] == l@[i as int] as int);
                assert(l@[i as int] >= t as int);
                assert(mapped_seq[i as int] >= t as int);
                assert(!(mapped_seq[i as int] < t as int));
                assert(!below_threshold(mapped_seq, t as int));
            }
            return false;
        }
        i += 1;
    }
    proof {
        let mapped_seq = l@.map(|_k: int, x: i8| x as int);
        assert(forall|j: int| 0 <= j < l.len() ==> {
            mapped_seq[j] == l@[j] as int && l@[j] < t as int
        });
        assert(forall|j: int| 0 <= j < mapped_seq.len() ==> mapped_seq[j] < t as int);
        assert(below_threshold(mapped_seq, t as int));
    }
    true
}
// </vc-code>


}

fn main() {}