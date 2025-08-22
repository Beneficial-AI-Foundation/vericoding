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

/* code modified by LLM (iteration 4): fixed function signature syntax by placing ensures clause after signature and before opening brace */
fn extract_first_digit(n: u32) -> (res: u32)
    decreases n,
    ensures res == extract_first_digit_spec(n as int),
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
// pure-end

/* code modified by LLM (iteration 4): fixed function signature syntax by placing ensures clause after signature and before opening brace */
fn extract_last_digit(n: u32) -> (res: u32)
    ensures res == extract_last_digit_spec(n as int),
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

/* code modified by LLM (iteration 4): fixed function signature syntax by placing ensures clause after signature and before opening brace */
fn is_valid_element(n: i32) -> (res: bool)
    ensures res == is_valid_element_spec(n as int),
{
    if n <= 10 {
        false
    } else {
        let n_abs = if n < 0 { (-n) as u32 } else { n as u32 };
        let first = extract_first_digit(n_abs);
        let last = extract_last_digit(n_abs);
        (first % 2 != 0) && (last % 2 != 0)
    }
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

/* code modified by LLM (iteration 4): fixed function signature syntax by placing ensures clause after signature and before opening brace */
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    ensures count == special_filter_spec(numbers@),
{
    let mut count = 0;
    let mut i = 0;
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int)),
    {
        if is_valid_element(numbers[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    assert(numbers@.take(numbers.len() as int) == numbers@);
    count
}

} // verus!
fn main() {}