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
fn is_valid_element(n: i32) -> bool {
    if n <= 10 {
        return false;
    }
    let last_digit = n % 10;
    if last_digit % 2 == 0 {
        return false;
    }
    let mut num = n;
    while num >= 10 {
        // invariant: num <= n && num >= 10
        num /= 10;
    }
    let first_digit = num;
    first_digit % 2 != 0
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
{
    let mut count = 0;
    for i in 0..numbers.len() {
        // invariant count == special_filter_spec(numbers@.prefix(i))
        let n = numbers[i];
        if is_valid_element(n) {
            count += 1;
        }
    }
    count
}
// </vc-code>

} // verus!
fn main() {}