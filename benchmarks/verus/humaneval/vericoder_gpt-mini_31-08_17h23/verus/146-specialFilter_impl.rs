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
fn extract_first_digit(n: i32) -> (ret: i32)
    requires n >= 0
    ensures ret as int == extract_first_digit_spec(n as int)
    decreases n
{
    if n < 10 {
        proof {
            assert(extract_first_digit_spec(n as int) == n as int);
        }
        n
    } else {
        let r = extract_first_digit(n / 10);
        proof {
            // By definition of spec, extract_first_digit_spec(n) == extract_first_digit_spec(n/10) when n >= 10
            assert(extract_first_digit_spec(n as int) == extract_first_digit_spec((n / 10) as int));
            // By induction hypothesis
            assert(r as int == extract_first_digit_spec((n / 10) as int));
            // Combine
            assert(r as int == extract_first_digit_spec(n as int));
        }
        r
    }
}

fn extract_last_digit(n: i32) -> (ret: i32)
    ensures ret as int == extract_last_digit_spec(n as int)
{
    let r: i32 = n % 10;
    proof {
        assert(r as int == extract_last_digit_spec(n as int));
    }
    r
}

fn is_valid_element(n: i32) -> (ret: bool)
    ensures ret == is_valid_element_spec(n as int)
{
    if n <= 10 {
        return false;
    }
    // n > 10 implies n >= 11, hence non-negative; safe to call extract_first_digit
    let first: i32 = extract_first_digit(n);
    let last: i32 = extract_last_digit(n);
    let cond: bool = ((first % 2) != 0) && ((last % 2) != 0);
    proof {
        // Relate runtime computations to spec-level functions
        assert(extract_first_digit_spec(n as int) == first as int);
        assert(extract_last_digit_spec(n as int) == last as int);
        assert(is_valid_element_spec(n as int) == (((n as int) > 10) && is_odd(extract_first_digit_spec(n as int)) && is_odd(extract_last_digit_spec(n as int))));
        // simplify using the above equalities
        assert(is_valid_element_spec(n as int) == (((n as int) > 10) && ((first % 2) != 0) && ((last % 2) != 0)));
        assert(is_valid_element_spec(n as int) == cond);
    }
    cond
}

proof fn special_filter_prefix_consistent(seq: Seq<i32>, i: nat)
    requires i < seq.len()
    ensures special_filter_spec(seq.slice(0, i + 1)) == special_filter_spec(seq.slice(0, i)) + (if is_valid_element_spec(seq@[i] as int) { 1 } else { 0 })
    decreases seq.len()
{
    let t = seq.slice(0, i + 1);
    proof {
        // By definition of special_filter_spec:
        assert(special_filter_spec(t) == special_filter_spec(t.drop_last()) + (if is_valid_element_spec(t.last() as int) { 1 } else { 0 }));
        // Relate t.drop_last() and t.last() to seq:
        assert(t.drop_last() == seq.slice(0, i));
        assert(t.last() == seq@[i]);
        // Combine equalities
        assert(special_filter_spec(seq.slice(0, i + 1)) == special_filter_spec(seq.slice(0, i)) + (if is_valid_element_spec(seq@[i] as int) { 1 } else { 0 }));
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
    // impl-start
    let mut i: usize = 0;
    let mut cnt: usize = 0;
    while i < numbers.len() {
        invariant i <= numbers.len();
        invariant (cnt as int) == special_filter_spec(numbers@.slice(0, i));
        let v: i32 = numbers.get(i);
        let valid: bool = is_valid_element(v);
        let add: usize = if valid { 1 } else { 0 };
        proof {
            // Use the prefix lemma to relate the spec for length i+1 to length i and the validity of element i
            special_filter_prefix_consistent(numbers@, i);
            // Relate runtime predicate to spec predicate
            assert(is_valid_element_spec(v as int) == is_valid_element(v));
            // From the invariant we have cnt as int == special_filter_spec(prefix length i)
            // So cnt as int + (if is_valid_element(v) {1} else {0}) == special_filter_spec(prefix length i+1)
            assert((cnt as int) + (if valid { 1 } else { 0 }) == special_filter_spec(numbers@.slice(0, i + 1)));
        }
        cnt = cnt + add;
        i += 1;
    }
    cnt
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}