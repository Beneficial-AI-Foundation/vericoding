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
proof fn extract_first_digit_spec_lemma(n: int)
    requires
        n >= 0,
    ensures
        extract_first_digit_spec(n) % 2 != 0 <==> is_odd(extract_first_digit_spec(n)),
    decreases n,
{
    if n >= 10 {
        extract_first_digit_spec_lemma(n / 10);
    }
}

proof fn extract_last_digit_spec_lemma(n: int)
    requires
        n >= 0,
    ensures
        extract_last_digit_spec(n) % 2 != 0 <==> is_odd(extract_last_digit_spec(n)),
{
}

proof fn special_filter_spec_lemma(seq: Seq<i32>, i: int)
    requires
        0 <= i <= seq.len() as int,
    ensures
        special_filter_spec(seq) == special_filter_spec(seq.take(i)) + special_filter_spec(seq.drop_last(seq.len() - i as usize)),
    decreases i,
{
    if i > 0 {
        special_filter_spec_lemma(seq, i - 1);
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
            0 <= i <= numbers@.len(),
            count == special_filter_spec(numbers@.take(i)),
        decreases numbers.len() - i,
    {
        let num = numbers[i];
        proof {
            let n = num as int;
            special_filter_spec_lemma(numbers@, i as int);
            if n > 10 {
                let first_digit = extract_first_digit_spec(n);
                let last_digit = extract_last_digit_spec(n);
                extract_first_digit_spec_lemma(n);
                extract_last_digit_spec_lemma(n);
            }
        }
        if num > 10 {
            proof {
                let n = num as int;
                let first_digit = extract_first_digit_spec(n);
                let last_digit = extract_last_digit_spec(n);
                assert(is_odd(first_digit) == (first_digit % 2 != 0));
                assert(is_odd(last_digit) == (last_digit % 2 != 0));
            }
            let n = num;
            let mut temp = n;
            while temp >= 10 {
                temp = temp / 10;
            }
            let first_digit = temp;
            let last_digit = n % 10;
            if first_digit % 2 != 0 && last_digit % 2 != 0 {
                count = count + 1;
            }
        }
        i = i + 1;
    }
    count
}
// </vc-code>

} // verus!
fn main() {}