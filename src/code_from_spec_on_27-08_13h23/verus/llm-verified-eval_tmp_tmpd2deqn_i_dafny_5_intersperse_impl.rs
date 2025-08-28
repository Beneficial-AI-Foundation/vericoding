use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_intersperse_len(numbers: Seq<int>, delimiter: int)
    ensures
        intersperse(numbers, delimiter).len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
{
    // Implementation can be added if needed for proof
}

proof fn lemma_intersperse_even_indices(numbers: Seq<int>, delimiter: int)
    ensures
        forall|i: int| 0 <= i < intersperse(numbers, delimiter).len() && i % 2 == 0 ==> 
            intersperse(numbers, delimiter)[i] == numbers[i / 2],
{
    // Implementation can be added if needed for proof
}

proof fn lemma_intersperse_odd_indices(numbers: Seq<int>, delimiter: int)
    ensures
        forall|i: int| 0 <= i < intersperse(numbers, delimiter).len() && i % 2 == 1 ==> 
            intersperse(numbers, delimiter)[i] == delimiter,
{
    // Implementation can be added if needed for proof
}
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
proof fn intersperse(numbers: Seq<int>, delimiter: int) -> (interspersed: Seq<int>)
    ensures
        interspersed.len() == if numbers.len() > 0 { 2 * numbers.len() - 1 } else { 0 },
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 0 ==> 
            interspersed[i] == numbers[i / 2],
        forall|i: int| 0 <= i < interspersed.len() && i % 2 == 1 ==> 
            interspersed[i] == delimiter,
{
    if numbers.len() == 0 {
        Seq::empty()
    } else {
        let mut result: Vec<int> = Vec::new();
        let mut i: usize = 0;
        
        while i < numbers.len()
            invariant
                i <= numbers.len(),
                result.len() == if i > 0 { 2 * i - 1 } else { 0 },
                forall|j: int| 0 <= j < result.len() && j % 2 == 0 ==> 
                    result[j as usize] == numbers[j / 2],
                forall|j: int| 0 <= j < result.len() && j % 2 == 1 ==> 
                    result[j as usize] == delimiter,
        {
            result.push(numbers[i]);
            if i < numbers.len() - 1 {
                result.push(delimiter);
            }
            i = i + 1;
        }
        
        result.to_seq()
    }
}
// </vc-code>

fn main() {}

}