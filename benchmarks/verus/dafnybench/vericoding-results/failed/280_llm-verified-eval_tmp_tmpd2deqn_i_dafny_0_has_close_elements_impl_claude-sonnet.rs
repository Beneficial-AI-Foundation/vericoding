use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x < 0 { -x } else { x }
}

// <vc-helpers>
proof fn lemma_close_elements_implies_length(numbers: Seq<int>, threshold: int)
    requires exists|i: int, j: int|
        0 <= i < numbers.len() &&
        0 <= j < numbers.len() &&
        i != j &&
        abs(numbers[i] - numbers[j]) < threshold
    ensures numbers.len() > 1
{
    let witness_i = choose|i: int| exists|j: int|
        0 <= i < numbers.len() &&
        0 <= j < numbers.len() &&
        i != j &&
        abs(numbers[i] - numbers[j]) < threshold;
    let witness_j = choose|j: int|
        0 <= witness_i < numbers.len() &&
        0 <= j < numbers.len() &&
        witness_i != j &&
        abs(numbers[witness_i] - numbers[j]) < threshold;
    
    assert(witness_i != witness_j);
    assert(0 <= witness_i < numbers.len());
    assert(0 <= witness_j < numbers.len());
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: Seq<int>, threshold: int) -> (result: bool)
    ensures
        result <==> exists|i: int, j: int|
            0 <= i < numbers.len() &&
            0 <= j < numbers.len() &&
            i != j &&
            abs(numbers[i] - numbers[j]) < threshold,
        result ==> numbers.len() > 1,
// </vc-spec>
// <vc-code>
{
    if numbers.len() <= 1 {
        return false;
    }
    
    for i in 0..(numbers.len() as usize)
        invariant
            forall|ii: int, jj: int|
                0 <= ii < i &&
                0 <= jj < numbers.len() &&
                ii != jj ==>
                abs(numbers[ii] - numbers[jj]) >= threshold
    {
        for j in 0..(numbers.len() as usize)
            invariant
                forall|ii: int, jj: int|
                    0 <= ii < i &&
                    0 <= jj < numbers.len() &&
                    ii != jj ==>
                    abs(numbers[ii] - numbers[jj]) >= threshold,
                forall|jj: int|
                    0 <= jj < j &&
                    i != jj ==>
                    abs(numbers[i as int] - numbers[jj]) >= threshold
        {
            let ii = i as int;
            let jj = j as int;
            if i != j && abs(numbers[ii] - numbers[jj]) < threshold {
                assert(exists|iii: int, jjj: int|
                    0 <= iii < numbers.len() &&
                    0 <= jjj < numbers.len() &&
                    iii != jjj &&
                    abs(numbers[iii] - numbers[jjj]) < threshold);
                proof {
                    lemma_close_elements_implies_length(numbers, threshold);
                }
                return true;
            }
        }
    }
    
    assert(forall|i: int, j: int|
        0 <= i < numbers.len() &&
        0 <= j < numbers.len() &&
        i != j ==>
        abs(numbers[i] - numbers[j]) >= threshold);
    
    false
}
// </vc-code>

fn main() {}

}