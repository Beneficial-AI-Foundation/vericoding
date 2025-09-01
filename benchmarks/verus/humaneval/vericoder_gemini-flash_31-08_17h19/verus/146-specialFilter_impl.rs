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
proof fn lemma_subsequence_add_one(s: Seq<i32>, val: i32, idx: int)
requires idx == s.len()
ensures s.add(val) == s.subsequence(0, idx) + Seq::singleton(val)
{}
proof fn lemma_special_filter_add_one(s: Seq<i32>, val: i32)
    ensures special_filter_spec(s.add(val)) == special_filter_spec(s) + if (val >= 0 && is_valid_element_spec(val as int)) { 1 } else { 0 }
{
    assert(special_filter_spec(s.add(val)) == special_filter_spec(s.add(val).drop_last()) +
           if (s.add(val).last() >= 0 && is_valid_element_spec(s.add(val).last() as int)) { 1 } else { 0 }) by(spec_arith);
    assert(s.add(val).drop_last() == s);
    assert(s.add(val).last() == val);
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

    #[verifier::loop_invariant(
        i <= numbers.len(),
        count == special_filter_spec(numbers@.subsequence(0, i as int)),
    )]
    while i < numbers.len() {
        let num = numbers.index(i);
        if num >= 0 && is_valid_element_spec(num as int) {
            count = count + 1;
        }
        i = i + 1;
        proof {
            assert(numbers@.subsequence(0, i as int) == numbers@.subsequence(0, (i - 1) as int).add(numbers@[i - 1]));
            lemma_special_filter_add_one(numbers@.subsequence(0, (i - 1) as int), numbers@[i - 1]);
        }
    }

    assert(count == special_filter_spec(numbers@));
    count
}
// </vc-code>

} // verus!
fn main() {}