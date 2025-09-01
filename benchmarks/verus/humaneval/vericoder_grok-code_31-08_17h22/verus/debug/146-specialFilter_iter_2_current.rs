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
fn extract_first_digit(n: int) -> (ret: int)
    decreases n
    ensures ret == extract_first_digit_spec(n)
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

fn extract_last_digit(n: int) -> (ret: int)
    ensures ret == extract_last_digit_spec(n)
{
    n % 10
}

fn is_odd(n: int) -> (ret: bool)
    ensures ret == ((n % 2) != 0)
{
    (n % 2) != 0
}

fn is_valid_element(n: int) -> (ret: bool)
    ensures ret == is_valid_element_spec(n)
{
    let first = extract_first_digit(n);
    let last = extract_last_digit(n);
    n > 10 && is_odd(first) && is_odd(last)
}
// </vc-helpers>

// <vc-spec>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    // post-conditions-start
    ensures
        count == special_filter_spec(numbers@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    ensures
        count == special_filter_spec(numbers@)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int))
    {
        if is_valid_element(numbers@[i as int]) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

} // verus!
fn main() {}