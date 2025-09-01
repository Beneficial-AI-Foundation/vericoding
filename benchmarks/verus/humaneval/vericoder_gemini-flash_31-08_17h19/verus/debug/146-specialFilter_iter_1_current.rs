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
spec fn extract_first_digit_spec(n: int) -> (ret:int)
    decreases n,
{
    if n < 10 {
        n
    } else {
        extract_first_digit_spec(n / 10)
    }
}
spec fn extract_last_digit_spec(n: int) -> (ret:int) {
    n % 10
}
spec fn is_odd(n: int) -> (ret:bool) {
    (n % 2) != 0
}

spec fn is_valid_element_spec(n: int) -> (ret:bool) {
    &&& (n > 10)
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
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

// Helper lemma for special_filter_spec property
// This lemma is generally not directly useful for this specific problem
// as the inductive proof for special_filter in the loop is more direct
/*
proof fn special_filter_inductive(s: Seq<i32>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        special_filter_spec(s.subsequence(0, i)) +
        special_filter_spec(s.subsequence(i, s.len())) ==
        special_filter_spec(s),
    decreases i,
{
    if i == 0 {
        assert(special_filter_spec(s.subsequence(0, 0)) == 0);
        assert(special_filter_spec(s.subsequence(0, s.len())) == special_filter_spec(s));
    } else if i == s.len() {
        assert(special_filter_spec(s.subsequence(0, s.len())) == special_filter_spec(s));
        assert(special_filter_spec(s.subsequence(s.len(), s.len())) == 0);
    } else {
        special_filter_inductive(s, i - 1);
        let prefix_i_minus_1 = s.subsequence(0, i - 1);
        let prefix_i = s.subsequence(0, i);
        let suffix_i_minus_1 = s.subsequence(i - 1, s.len());
        let suffix_i = s.subsequence(i, s.len());

        assert(special_filter_spec(prefix_i) == special_filter_spec(prefix_i_minus_1) + if (is_valid_element_spec(s.index(i-1) as int)) { 1 } else { 0 });
        assert(special_filter_spec(s) == special_filter_spec(s.drop_last()) + if (is_valid_element_spec(s.last() as int)) { 1 } else { 0 });
    }
}
*/
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

    #[veri_annotations::invariants(
        i <= numbers.len(),
        count == special_filter_spec(numbers.view().subsequence(0, i as int)),
    )]
    while i < numbers.len() {
        let num = numbers.index(i);
        if is_valid_element_spec(num as int) {
            count = count + 1;
        }
        i = i + 1;
    }

    assert(count == special_filter_spec(numbers.view().subsequence(0, numbers.len() as int)));
    count
}
// </vc-code>

} // verus!
fn main() {}