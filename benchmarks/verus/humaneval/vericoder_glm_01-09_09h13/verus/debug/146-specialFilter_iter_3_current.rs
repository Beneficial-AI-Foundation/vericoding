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
proof fn special_filter_spec_add_element(seq: Seq<i32>, n: int)
    ensures
        special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }),
{
    if seq.len() == 0 {
        assert(special_filter_spec(Seq::empty().push(n as i32)) == if is_valid_element_spec(n) { 1 } else { 0 });
    } else {
        special_filter_spec_add_element(seq.drop_last(), seq.last() as int);
        assert(special_filter_spec(seq) == special_filter_spec(seq.drop_last()) + (if is_valid_element_spec(seq.last() as int) { 1 } else { 0 }));
        assert(special_filter_spec(seq.drop_last().push(n as i32)) == special_filter_spec(seq.drop_last()) + (if is_valid_element_spec(n) { 1 } else { 0 }));
        if is_valid_element_spec(seq.last() as int) && is_valid_element_spec(n) {
            assert(special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq.drop_last().push(seq.last()).push(n as i32)));
        } else if is_valid_element_spec(seq.last() as int) {
            assert(special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq.drop_last().push(seq.last()).push(n as i32)));
        } else if is_valid_element_spec(n) {
            assert(special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq.drop_last().push(seq.last()).push(n as i32)));
        } else {
            assert(special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq.drop_last().push(seq.last()).push(n as i32)));
        }
    }
}

proof fn lemma_seq_take_push(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        seq.take(i).push(seq@[i]) == seq.take(i + 1),
{
    if i == 0 {
        assert(Seq::empty().push(seq@[0]) == seq.take(1));
    } else {
        lemma_seq_take_push(seq.drop_first(), i - 1);
    }
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
    let old_numbers = numbers@;

    while i < numbers.len()
        invariant
            old_numbers == numbers@,
            special_filter_spec(old_numbers.take(i as int)) == count,
            0 <= i <= numbers.len(),
    {
        let current_value = numbers[i] as int;
        proof {
            lemma_seq_take_push(old_numbers, i as int);
        }
        if is_valid_element_spec(current_value) {
            count += 1;
            proof {
                special_filter_spec_add_element(old_numbers.take(i as int), current_value);
                assert(special_filter_spec(old_numbers.take(i as int
// </vc-code>

} // verus!
fn main() {}