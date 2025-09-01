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
        assert(seq.take(0) == Seq::<i32>::empty());
        assert(seq.take(0).push(seq@[0]) == Seq::singleton(seq@[0]));
        assert(seq.take(1) == Seq::singleton(seq@[0]));
    } else {
        assert(seq.take(i).push(seq@[i]) == seq.take(i + 1));
    }
}

proof fn special_filter_spec_eq_lemma(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len(),
    ensures
        special_filter_spec(seq) == special_filter_spec(seq.take(i)) + special_filter_spec(seq.drop(i)),
{
    if i == 0 {
        assert(seq.take(0) == Seq::<i32>::empty());
        assert(seq.drop(0) == seq);
        assert(special_filter_spec(seq) == special_filter_spec(Seq::empty()) + special_filter_spec(seq));
        assert(special_filter_spec(Seq::empty()) == 0);
        assert(special_filter_spec(seq) == 0 + special_filter_spec(seq));
    } else if i == seq.len() {
        assert(seq.take(i) == seq);
        assert(seq.drop(i) == Seq::<i32>::empty());
        assert(special_filter_spec(seq) == special_filter_spec(seq) + special_filter_spec(Seq::empty()));
        assert(special_filter_spec(Seq::empty()) == 0);
        assert(special_filter_spec(seq) == special_filter_spec(seq) + 0);
    } else {
        special_filter_spec_eq_lemma(seq, 0);
        special_filter_spec_eq_lemma(seq, seq.len());
        assert(seq.take(i).push(seq@[i]) == seq.take(i + 1));
        special_filter_spec_add_element(seq.take(i), seq@[i] as int);
        special_filter_spec_eq_lemma(seq.drop(i), 1);
        special_filter_spec_eq_lemma(seq.take(i), i - 1);
        special_filter_spec_eq_lemma(seq.drop(i - 1), 1);
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
    
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count == special_filter_spec(numbers@.take(i as int)),
    {
        let n = numbers@[i] as int;
        if is_valid_element_spec(n) {
            count += 1;
            special_filter_spec_add_element(numbers@.take(i as int), n);
            assert(special_filter_spec(numbers@.take(i as int).push(n as i32)) == special_filter_spec(numbers@.take(i as int)) + 1);
            lemma_seq_take_push(numbers@, i as int);
            assert(numbers@.take(i as int).push(n as i32) == numbers@.take(i as int + 1));
            assert(special_filter_spec(numbers@.take(i as int + 1)) == special_filter_spec(numbers@.take(i as int)) + 1);
        }
        i += 1;
    }
    assert(i == numbers.len());
    assert(numbers@.take(i as int) == numbers@);
    assert(count == special_filter_spec(numbers@));
    count
}
// </vc-code>

} // verus!
fn main() {}