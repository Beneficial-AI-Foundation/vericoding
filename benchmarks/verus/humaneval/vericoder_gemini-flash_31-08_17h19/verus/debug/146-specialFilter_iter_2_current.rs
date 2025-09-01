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
spec fn extract_first_digit_spec(n: int) -> int
    decreases n
{
    if n < 10 {
        n
    } else {
        extract_first_digit_spec(n / 10)
    }
}
spec fn extract_last_digit_spec(n: int) -> int {
    n % 10
}
spec fn is_odd(n: int) -> bool {
    (n % 2) != 0
}

spec fn is_valid_element_spec(n: int) -> bool {
    &&& (n > 10)
    &&& (n >= 0) // Ensure n is non-negative for digit extraction
    &&& is_odd(extract_first_digit_spec(n))
    &&& is_odd(extract_last_digit_spec(n))
}

spec fn special_filter_spec(seq: Seq<i32>) -> int
    decreases seq.len()
{
    if seq.len() == 0 {
        0
    } else {
        special_filter_spec(seq.drop_last()) + if (seq.last() >= 0 && is_valid_element_spec(seq.last() as int)) {
            1
        } else {
            0
        }
    }
}

proof fn lemma_subsequence_count(s: Seq<i32>, idx: int)
    requires 0 <= idx <= s.len()
    ensures special_filter_spec(s.subsequence(0, idx)) + special_filter_spec(s.subsequence(idx, s.len())) == special_filter_spec(s)
    decreases idx
{
    if idx == 0 {
        assert(special_filter_spec(s.subsequence(0, 0)) == 0);
        assert(s.subsequence(0, s.len()) == s);
    } else if idx == s.len() {
        assert(s.subsequence(0, s.len()) == s);
        assert(special_filter_spec(s.subsequence(s.len(), s.len())) == 0);
    } else {
        lemma_subsequence_count(s, idx + 1);
        // This lemma is not directly used in the current while loop proof,
        // but it's a general property that might be useful for other proofs.
    }
}

// proof of `special_filter_spec` equivalence with single element removal
proof fn lemma_special_filter_add_one(s: Seq<i32>, val: i32)
    ensures special_filter_spec(s.add(val)) == special_filter_spec(s) + if (val >= 0 && is_valid_element_spec(val as int)) { 1 } else { 0 }
{
    assert(special_filter_spec(s.add(val)) == special_filter_spec(s.add(val).drop_last()) +
           if (s.add(val).last() >= 0 && is_valid_element_spec(s.add(val).last() as int)) { 1 } else { 0 });
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

    #[invariant(
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
            lemma_special_filter_add_one(numbers@.subsequence(0, (i - 1) as int), numbers@[i - 1]);
        }
    }

    assert(count == special_filter_spec(numbers@));
    count
}
// </vc-code>

} // verus!
fn main() {}