use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let sn: Seq<int> = numbers.to_seq();
    let mut i: nat = 0; // Changed to nat
    while i < sn.len()
        invariant
            0 <= i,
            i <= sn.len(),
            count == sn.subsequence(0, i).filter(|k: int| k < threshold).len(),
            sn.to_set() =~= numbers
    {
        if sn.index(i) < threshold {
            count = count + 1;
        }
        i = i + 1;
    }
    proof {
        assert(sn.to_set() =~= numbers);
        assert(sn.subsequence(0, sn.len()).filter(|k: int| k < threshold).len() == numbers.filter(|k: int| k < threshold).len());
    }
    count
}
// </vc-code>

fn main() {}

}