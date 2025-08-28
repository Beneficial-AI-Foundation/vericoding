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
fn extract_first_digit(n: u32) -> (res: u32)
    decreases n
    ensures
        res == extract_first_digit_spec(n as int),
{
    if n < 10 {
        n
    } else {
        extract_first_digit(n / 10)
    }
}

fn extract_last_digit(n: u32) -> (res: u32)
    ensures
        res == extract_last_digit_spec(n as int),
{
    n % 10
}

fn is_valid_element(n: i32) -> (res: bool)
    ensures
        res == is_valid_element_spec(n as int),
{
    ((n > 10) && (extract_first_digit(n as u32) % 2 != 0) && (extract_last_digit(n as u32) % 2
        != 0))
}

proof fn special_filter_lemma(numbers: Seq<i32>, i: nat)
    requires i <= numbers.len()
    ensures special_filter_spec(numbers.take(i as int)) == special_filter_spec(numbers.subrange(0, i as int))
{
}

proof fn special_filter_prefix_lemma(numbers: Seq<i32>, i: nat)
    requires i < numbers.len()
    ensures special_filter_spec(numbers.take(i as int + 1)) == 
        special_filter_spec(numbers.take(i as int)) + 
        if is_valid_element_spec(numbers[i as int] as int) { 1int } else { 0int }
{
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
            count == special_filter_spec(numbers@.take(i as int)),
    {
        if is_valid_element(numbers[i]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>

} // verus!
fn main() {}