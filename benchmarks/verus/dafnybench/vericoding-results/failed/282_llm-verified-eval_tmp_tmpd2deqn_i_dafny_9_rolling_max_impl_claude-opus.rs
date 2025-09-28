use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
// Helper lemma: if m is the max of numbers[0..i], then max(m, numbers[i]) is the max of numbers[0..i+1]
proof fn lemma_max_extension(numbers: Seq<int>, i: int, current_max: int)
    requires
        0 <= i < numbers.len(),
        i == 0 || isMax(current_max, numbers.subrange(0, i)),
    ensures
        isMax(
            if i == 0 { numbers[0] } else if numbers[i] > current_max { numbers[i] } else { current_max },
            numbers.subrange(0, i + 1)
        ),
{
    let new_max = if i == 0 { numbers[0] } else if numbers[i] > current_max { numbers[i] } else { current_max };
    
    // Prove that new_max is in the subrange
    assert(numbers.subrange(0, i + 1).len() == i + 1);
    assert(numbers.subrange(0, i + 1)[i] == numbers[i]);
    
    if i == 0 {
        assert(numbers.subrange(0, 1).len() == 1);
        assert(numbers.subrange(0, 1)[0] == numbers[0]);
        assert(numbers.subrange(0, 1).contains(new_max));
        assert(forall|j: int| 0 <= j < 1 ==> #[trigger] numbers.subrange(0, 1)[j] <= new_max);
    } else {
        // new_max is either current_max or numbers[i]
        if numbers[i] > current_max {
            assert(new_max == numbers[i]);
            assert(numbers.subrange(0, i + 1).contains(new_max));
            
            // All elements in [0..i) are <= current_max < numbers[i] = new_max
            assert(forall|j: int| 0 <= j < i ==> #[trigger] numbers.subrange(0, i)[j] <= current_max);
            assert(forall|j: int| 0 <= j < i ==> #[trigger] numbers.subrange(0, i + 1)[j] == numbers[j]);
            assert(forall|j: int| 0 <= j < i ==> #[trigger] numbers.subrange(0, i + 1)[j] <= new_max);
            assert(numbers.subrange(0, i + 1)[i] == numbers[i] == new_max);
            assert(forall|j: int| 0 <= j < i + 1 ==> #[trigger] numbers.subrange(0, i + 1)[j] <= new_max);
        } else {
            assert(new_max == current_max);
            assert(isMax(current_max, numbers.subrange(0, i)));
            
            // current_max is in numbers.subrange(0, i), which is contained in numbers.subrange(0, i + 1)
            assert(exists|k: int| 0 <= k < i && #[trigger] numbers.subrange(0, i)[k] == current_max);
            let k_witness = choose|k: int| 0 <= k < i && numbers.subrange(0, i)[k] == current_max;
            assert(numbers.subrange(0, i + 1)[k_witness] == current_max);
            assert(numbers.subrange(0, i + 1).contains(new_max));
            
            // All elements in [0..i) are <= current_max = new_max
            assert(forall|j: int| 0 <= j < i ==> #[trigger] numbers.subrange(0, i + 1)[j] <= new_max);
            // Element at i is <= current_max = new_max (by our condition)
            assert(numbers.subrange(0, i + 1)[i] == numbers[i] <= current_max == new_max);
            assert(forall|j: int| 0 <= j < i + 1 ==> #[trigger] numbers.subrange(0, i + 1)[j] <= new_max);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    let mut current_max: int = numbers[0];
    
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            i > 0 ==> isMax(current_max, numbers@.subrange(0, i as int)),
            forall|j: int| 0 < j < i ==> #[trigger] isMax(result[j], numbers@.subrange(0, j + 1)),
        decreases numbers.len() - i,
    {
        if i == 0 {
            current_max = numbers[0];
        } else {
            if numbers[i as usize] > current_max {
                current_max = numbers[i as usize];
            }
        }
        
        proof {
            lemma_max_extension(numbers@, i as int, current_max);
        }
        
        result.push(current_max);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}