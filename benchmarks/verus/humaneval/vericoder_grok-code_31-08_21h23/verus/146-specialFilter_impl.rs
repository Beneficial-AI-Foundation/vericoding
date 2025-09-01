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
fn extract_last_digit(n: i32) -> (ret: i32)
    requires
        n > 10,
    ensures
        ret as int == extract_last_digit_spec(n as int),
{
    n % 10
}

fn extract_first_digit(n: i32) -> (ret: i32)
    requires
        n > 10,
    ensures
        ret as int == extract_first_digit_spec(n as int),
{
    let mut m = n;
    proof {
        if n >= 10 {
            assert(extract_first_digit_spec(n as int) == extract_first_digit_spec((n / 10) as int));
        }
    }
    while m >= 10
        invariant
            decreases m,
            m > 0,
            extract_first_digit_spec(m as int) == extract_first_digit_spec(n as int),
    {
        m = m / 10;
    }
    m
}

fn odd(n: i32) -> (ret: bool)
    ensures
        ret == is_odd(n as int),
{
    (n % 2) != 0
}

fn is_valid_element(n: i32) -> (ret: bool)
    ensures
        ret == is_valid_element_spec(n as int),
{
    &&& (n > 10)
    &&& odd(extract_first_digit(n))
    &&& odd(extract_last_digit(n))
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
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            count as int == special_filter_spec(numbers@.subrange(0, i as int)),
    {
        let x = numbers[i];
        if x > 10 && is_valid_element(x) {
            proof {
                assert(is_valid_element_spec(x as int) == is_valid_element(x));
                assert(special_filter_spec(numbers@.subrange(0, i as int + 1)) == special_filter_spec(numbers@.subrange(0, i as int)) + if is_valid_element_spec(x as int) { 1 as int } else { 0 as int });
            }
            count += 1;
        }

        i += 1;
    }
    count
}
// </vc-code>

} // verus!
fn main() {}