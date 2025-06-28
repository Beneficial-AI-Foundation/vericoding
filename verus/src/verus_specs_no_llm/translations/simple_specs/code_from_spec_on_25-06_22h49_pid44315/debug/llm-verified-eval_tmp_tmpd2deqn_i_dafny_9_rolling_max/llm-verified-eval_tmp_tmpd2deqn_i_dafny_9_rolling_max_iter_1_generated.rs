use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn isMax(max_val: int, seq: Seq<int>) -> bool {
    seq.len() > 0 && 
    (exists i :: 0 <= i < seq.len() && seq.spec_index(i) == max_val) &&
    (forall j :: 0 <= j < seq.len() ==> seq.spec_index(j) <= max_val)
}

fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires
        numbers.len() > 0
    ensures
        result.len() == numbers.len(),
        forall i :: 0 <= i < result.len() ==> isMax(result.spec_index(i), numbers.spec_index(0..(i+1)))
{
    let mut result = Seq::empty();
    let mut current_max = numbers.spec_index(0);
    result = result.push(current_max);
    
    let mut idx = 1;
    while idx < numbers.len()
        invariant
            1 <= idx <= numbers.len(),
            result.len() == idx,
            forall i :: 0 <= i < result.len() ==> isMax(result.spec_index(i), numbers.spec_index(0..(i+1)))
    {
        if numbers.spec_index(idx) > current_max {
            current_max = numbers.spec_index(idx);
        }
        result = result.push(current_max);
        idx = idx + 1;
    }
    
    result
}

}