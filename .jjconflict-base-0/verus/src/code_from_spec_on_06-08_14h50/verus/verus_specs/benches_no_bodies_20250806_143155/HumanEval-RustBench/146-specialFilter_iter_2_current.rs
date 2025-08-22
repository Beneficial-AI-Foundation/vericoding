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

fn extract_first_digit(n: u32) -> (res: u32)
    // post-conditions-start
    ensures
        res == extract_first_digit_spec(n as int),
    // post-conditions-end
{
    let mut current = n;
    while current >= 10
        invariant
            extract_first_digit_spec(current as int) == extract_first_digit_spec(n as int),
        decreases current,
    {
        current = current / 10;
    }
    current
}

spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
// pure-end

fn extract_last_digit(n: u32) -> (res: u32)
    // post-conditions-start
    ensures
        res == extract_last_digit_spec(n as int),
    // post-conditions-end
{
    n % 10
}

spec fn is_odd(n: int) -> (ret:bool) {
    (n % 2) != 0
}
// pure-end

spec fn is_valid_element_spec(n: int) -> (ret:bool) {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}
// pure-end

fn is_valid_element(n: i32) -> (res: bool)
    // post-conditions-start
    ensures
        res == is_valid_element_spec(n as int),
    // post-conditions-end
{
    if n <= 10 {
        return false;
    }
    
    let first_digit = extract_first_digit(n as u32);
    let last_digit = extract_last_digit(n as u32);
    
    let first_odd = (first_digit % 2) != 0;
    let last_odd = (last_digit % 2) != 0;
    
    first_odd && last_odd
}

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

fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    // post-conditions-start
    ensures
        count == special_filter_spec(numbers@),
    // post-conditions-end
{
    let mut count = 0;
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int)),
        /* code modified by LLM (iteration 1): added decreases clause to fix termination verification */
        decreases numbers.len() - i,
    {
        if is_valid_element(numbers[i]) {
            count += 1;
        }
        i += 1;
    }
    
    proof {
        assert(numbers@.take(numbers@.len() as int) == numbers@);
    }
    
    count
}

} // verus!
fn main() {}