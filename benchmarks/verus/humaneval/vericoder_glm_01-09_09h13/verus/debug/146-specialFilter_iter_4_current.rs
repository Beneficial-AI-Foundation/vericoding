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
        let s = Seq::singleton(n as i32);
        assert(s == Seq::singleton(n as i32));
        assert(special_filter_spec(s) == special_filter_spec(s.drop_last()) + (if is_valid_element_spec(s.last() as int) { 1 } else { 0 }));
        assert(s.drop_last() == Seq::empty());
        assert(s.last() == n as i32);
        assert(special_filter_spec(s) == special_filter_spec(Seq::empty()) + (if is_valid_element_spec(n) { 1 } else { 0 }));
        assert(special_filter_spec(Seq::empty()) == 0);
        assert(special_filter_spec(s) == (if is_valid_element_spec(n) { 1 } else { 0 }));
        assert(special_filter_spec(seq) == 0);
        assert(special_filter_spec(s) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }));
    } else {
        let s = seq.push(n as i32);
        assert(special_filter_spec(s) == special_filter_spec(s.drop_last()) + (if is_valid_element_spec(s.last() as int) { 1 } else { 0 }));
        assert(s.drop_last() == seq);
        assert(s.last() == n as i32);
        assert(special_filter_spec(s) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }));
    }
}

proof fn lemma_seq_take_push(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        seq.take(i).push(seq@[i]) == seq.take(i + 1),
{
    if i == 0 {
        assert
// </vc-helpers>

// <vc-spec>
fn special_filter(numbers: &Vec<i32>) -> (count: usize)
    // post-conditions-start
    ensures
        count == special_filter_spec(numbers@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
proof fn special_filter_spec_add_element(seq: Seq<i32>, n: int)
    ensures
        special_filter_spec(seq.push(n as i32)) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }),
{
    if seq.len() == 0 {
        let s = Seq::singleton(n as i32);
        assert(s == Seq::singleton(n as i32));
        assert(special_filter_spec(s) == special_filter_spec(s.drop_last()) + (if is_valid_element_spec(s.last() as int) { 1 } else { 0 }));
        assert(s.drop_last() == Seq::empty());
        assert(s.last() == n as i32);
        assert(special_filter_spec(s) == special_filter_spec(Seq::empty()) + (if is_valid_element_spec(n) { 1 } else { 0 }));
        assert(special_filter_spec(Seq::empty()) == 0);
        assert(special_filter_spec(s) == (if is_valid_element_spec(n) { 1 } else { 0 }));
        assert(special_filter_spec(seq) == 0);
        assert(special_filter_spec(s) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }));
    } else {
        let s = seq.push(n as i32);
        assert(special_filter_spec(s) == special_filter_spec(s.drop_last()) + (if is_valid_element_spec(s.last() as int) { 1 } else { 0 }));
        assert(s.drop_last() == seq);
        assert(s.last() == n as i32);
        assert(special_filter_spec(s) == special_filter_spec(seq) + (if is_valid_element_spec(n) { 1 } else { 0 }));
    }
}

proof fn lemma_seq_take_push(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        seq.take(i).push(seq@[i]) == seq.take(i + 1),
{
    if i == 0 {
        assert
// </vc-code>

} // verus!
fn main() {}