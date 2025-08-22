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
    return 0;  // TODO: Remove this line and implement the function body
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
    return 0;  // TODO: Remove this line and implement the function body
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
    return false;  // TODO: Remove this line and implement the function body
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
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!
fn main() {}
