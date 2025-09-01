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
proof fn special_filter_spec_ignores_last(seq: Seq<i32>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        special_filter_spec(seq) == special_filter_spec(seq.update(i, 0)),
{
    if seq.len() == 0 {
        assert(false);
    }
    if i < seq.len() - 1 {
        special_filter_spec_ignores_last(seq.drop_last(), i);
        assert(special_filter_spec(seq.drop_last()) == special_filter_spec(seq.drop_last().update(i, 0)));
        assert(seq.update(i, 0).drop_last() == seq.drop_last().update(i, 0));
        assert(special_filter_spec(seq) == special_filter_spec(seq.update(i, 0)));
    } else {
        assert(seq.update(i, 0).last() == 0);
        assert(special_filter_spec(seq) == special_filter_spec(seq.drop_last()) + (if is_valid_element_spec(seq.last() as int) { 1 } else { 0 }));
        assert(special_filter_spec(seq.update(i, 0)) == special_filter_spec(seq.update(i, 0).drop_last()) + (if is_valid_element_spec(0) { 1 } else { 0 }));
        assert(special_filter_spec(seq.drop_last()) == special_filter_spec(seq.update(i, 0).drop_last()));
        assert(!is_valid_element_spec(0));
        assert(special_filter_spec(seq) == special_filter_spec(seq.update(i, 0)));
    }
}

proof fn lemma_seq_drop_last_all(seq: Seq<i32>)
    decreases seq.len(),
    ensures
        seq.drop_last().len() == seq.len() - 1,
{
    if seq.len() == 0 {
        assert(seq.drop_last().len() == 0);
        assert(seq.len() - 1 == -1);
    } else {
        lemma_seq_drop_last_all(seq.drop_last());
        assert(seq.drop_last().drop_last().len() == seq.drop_last().len() - 1);
        assert(seq.drop_last().len() == seq.len() - 1);
    }
}

proof fn lemma_seq_index_last(seq: Seq<i32>)
    requires
        seq.len() > 0,
    ensures
        seq@[seq.len() - 1] == seq.last(),
{
    lemma_seq_drop_last_all(seq);
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
            lemma_seq_index_last(old_numbers.take(i as int + 1));
        }
        if is_valid_element_spec(current_value) {
            count += 1;
        }
        i += 1;
    }
    proof {
        assert(old_numbers == numbers@);
        assert(special_filter_spec(old_numbers.take(i as int)) == count);
        assert(special_filter_spec(old_numbers) == special_filter_spec(old_numbers.take(i as int)));
    }
    count
}
// </vc-code>

} // verus!
fn main() {}