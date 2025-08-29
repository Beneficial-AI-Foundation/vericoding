use vstd::prelude::*;

verus! {

spec fn extract_first_digit_spec(n: int) -> (ret:int)
    decreases n,
{
    if n < 10 {
        n
    } else {
        extract_first_digit_spec(n / 10)
    }
}
// pure-end
spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
// pure-end
spec fn is_odd(n: int) -> (ret:bool) {
    (n % 2) != 0
}
// pure-end
// pure-end


spec fn is_valid_element_spec(n: int) -> (ret:bool) {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}
// pure-end
spec fn special_filter_spec(seq: Seq<i32>) -> (ret:int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        special_filter_spec(seq.drop_last()) + if (is_valid_element_spec(seq.last() as int)) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_special_filter_spec_extend(seq: Seq<i32>, elem: i32)
    ensures special_filter_spec(seq.push(elem)) == special_filter_spec(seq) + if is_valid_element_spec(elem as int) { 1int } else { 0int }
{
    let extended = seq.push(elem);
    assert(extended.drop_last() == seq);
    assert(extended.last() == elem);
}

proof fn lemma_special_filter_spec_empty()
    ensures special_filter_spec(Seq::<i32>::empty()) == 0
{
}

proof fn lemma_usize_to_int_bounds(count: usize, max_val: usize)
    requires count <= max_val
    ensures count as int <= max_val as int
{
}

proof fn lemma_count_increment_bound(count: usize, len: usize)
    requires count < len
    ensures count + 1 <= len
{
}

fn extract_first_digit(n: i32) -> (ret: i32)
    requires n >= 0
    ensures ret == extract_first_digit_spec(n as int)
    decreases n
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

fn is_valid_element(n: i32) -> (ret: bool)
    ensures ret == is_valid_element_spec(n as int)
{
    if n <= 10 {
        false
    } else {
        let first_digit = extract_first_digit(n);
        let last_digit = n % 10;
        let first_odd = (first_digit % 2) != 0;
        let last_odd = (last_digit % 2) != 0;
        first_odd && last_odd
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def specialFilter(nums: List[int]) -> int"
docstring: |
Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
test_cases:
- input: [15, -73, 14, -15]
expected_output: 1
- input: [33, -2, -3, 45, 21, 109]
expected_output: 2
*/
// </vc-description>

// <vc-spec>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    // post-conditions-start
    ensures
        count == special_filter_spec(numbers@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count = 0usize;
    let mut i = 0usize;
    
    proof {
        lemma_special_filter_spec_empty();
    }
    
    /* code modified by LLM (iteration 5): added overflow prevention and proper invariant maintenance */
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int)),
        decreases numbers.len() - i
    {
        let current = numbers[i];
        let is_valid = is_valid_element(current);
        
        proof {
            lemma_special_filter_spec_extend(numbers@.take(i as int), current);
            assert(numbers@.take((i + 1) as int) == numbers@.take(i as int).push(current));
        }
        
        if is_valid {
            /* code modified by LLM (iteration 5): prevent overflow with bounds check */
            if count < numbers.len() {
                proof {
                    lemma_count_increment_bound(count, numbers.len());
                }
                count = count + 1;
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(numbers@.take(numbers.len() as int) == numbers@);
    }
    
    count
}
// </vc-code>

} // verus!
fn main() {}