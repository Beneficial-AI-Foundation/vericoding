use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemmas for sequence indexing
proof fn lemma_seq_index_bounds(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures s[i] == s[i]
{}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==>
            interspersed[i] == delimiter,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==>
            interspersed[i] == delimiter,
{
    if numbers.len() == 0 {
        seq![]
    } else {
        let mut result = seq![numbers[0]];
        let mut i: int = 1;
        while i < numbers.len()
            invariant
                1 <= i <= numbers.len(),
                result.len() == 2 * i - 1,
                forall|j: int| 0 <= j < result.len() && j % 2 == 0 ==>
                    result[j] == numbers[j / 2],
                forall|j: int| 0 <= j < result.len() && j % 2 == 1 ==>
                    result[j] == delimiter,
        {
            result = result.push(delimiter);
            result = result.push(numbers[i]);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

fn main() {}

}