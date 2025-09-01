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
// No additional helper functions needed.
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
    let mut acc: int = 0;
    let len = numbers.len();
    while i < len
        invariant
            i <= len,
            0 <= acc,
            acc <= len as int,
            acc == special_filter_spec(numbers@.slice(0, i)),
        decreases len - i
    {
        let v: i32 = numbers[i];

        let mut is_valid: bool = false;
        if (v as int) > 10 {
            let ov: i32 = v;
            let mut m: i32 = ov;
            // invariant: extract_first_digit_spec(ov) == extract_first_digit_spec(m)
            proof {
                assert(extract_first_digit_spec(ov as int) == extract_first_digit_spec(m as int));
            }
            while m >= 10
                invariant
                    extract_first_digit_spec(ov as int) == extract_first_digit_spec(m as int),
                decreases m
            {
                m /= 10;
                proof {
                    // From spec definition: if m_old >= 10 then extract_first_digit_spec(m_old) == extract_first_digit_spec(m_old/10)
                    // Using previous invariant, we get extract_first_digit_spec(ov) == extract_first_digit_spec(m)
                    assert(extract_first_digit_spec(ov as int) == extract_first_digit_spec(m as int));
                }
            }
            // Now m < 10, so extract_first_digit_spec(ov) == m
            proof {
                assert(extract_first_digit_spec(ov as int) == m as int);
                assert(extract_last_digit_spec(ov as int) == (ov % 10) as int);
                assert(is_odd(extract_first_digit_spec(ov as int)) == ((m % 2) != 0));
                assert(is_odd(extract_last_digit_spec(ov as int)) == (((ov % 10) % 2) != 0));
                assert(is_valid_element_spec(ov as int) == (((ov as int) > 10) && ((m % 2) != 0) && (((ov % 10) % 2) != 0)));
            }
            is_valid = ((m % 2) != 0) && (((v % 10) % 2) != 0);
        } else {
            is_valid = false;
        }

        if is_valid {
            acc += 1;
        }

        proof {
            // relate runtime v and spec element numbers@[i]
            assert(numbers@[i] == (v as int));
            // By definition of special_filter_spec on sequences, extending the prefix by the i-th element:
            assert(special_filter_spec(numbers@.slice(0, i+1)) ==
                   special_filter_spec(numbers@.slice(0, i)) + (if is_valid_element_spec(numbers@[i]) { 1 as int } else { 0 as int }));
            // show that the runtime boolean equals the spec predicate for this element
            if (v as int) > 10 {
                // we proved above the equivalence when v > 10
                assert(is_valid_element_spec(numbers@[i]) == is_valid);
            } else {
                assert(!is_valid);
                assert(!is_valid_element_spec(numbers@[i]));
            }
            // conclude the accumulator matches the spec for the extended prefix
            if is_valid {
                assert(acc == special_filter_spec(numbers@.slice(0, i)) + 1);
            } else {
                assert(acc == special_filter_spec(numbers@.slice(0, i)));
            }
            assert(acc == special_filter_spec(numbers@.slice(0, i+1)));
        }

        i += 1;
    }

    // acc is non-negative and equals the spec result; cast to usize for return
    let result: usize = acc as usize;
    result
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}