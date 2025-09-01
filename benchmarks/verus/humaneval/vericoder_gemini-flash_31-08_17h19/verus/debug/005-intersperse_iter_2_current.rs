use vstd::assert_seqs_equal;
use vstd::prelude::*;

verus! {

spec fn intersperse_spec(numbers: Seq<u64>, delimiter: u64) -> (result:Seq<u64>)
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]
    }
}
// pure-end
// pure-end

spec fn even(i: int) -> (result:int) {
    2 * i
}
// pure-end
// pure-end

spec fn odd(i: int) -> (result:int) {
    2 * i + 1
}
// pure-end
// pure-end

spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> (result:bool) {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}
// pure-end

// <vc-helpers>
use vstd::prelude::*;

spec fn intersperse_spec(numbers: Seq<u64>, delimiter: u64) -> (result:Seq<u64>)
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        numbers
    } else {
        intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]
    }
}
// pure-end

spec fn even(i: int) -> int {
    2 * i
}
// pure-end

spec fn odd(i: int) -> int {
    2 * i + 1
}
// pure-end

spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> (result:bool) {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}
// pure-end

proof fn lemma_intersperse_spec_len_even(
    numbers: Seq<u64>,
    delimiter: u64,
    i: int,
)
    requires
        0 <= i < numbers.len(),
    ensures
        intersperse_spec(numbers, delimiter).len() == (if numbers.len() == 0 { 0 } else { 2 * numbers.len() - 1 }),
        intersperse_spec(numbers, delimiter)[even(i)] == numbers[i],
    decreases numbers.len(),
{
    if numbers.len() == 0 {
        assert(intersperse_spec(numbers, delimiter).len() == 0);
    } else if numbers.len() == 1 {
        assert(intersperse_spec(numbers, delimiter).len() == 1);
        assert(intersperse_spec(numbers, delimiter)[even(0)] == numbers[0]);
    } else {
        proof {
            lemma_intersperse_spec_len_even(numbers.drop_last(), delimiter, i);
        }
        assert(intersperse_spec(numbers, delimiter).len() == intersperse_spec(numbers.drop_last(), delimiter).len() + 2);
        assert_by_contradiction!(intersperse_spec(numbers, delimiter).len() == (2 * (numbers.drop_last()).len() - 1) + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * (numbers.len() - 1) - 1 + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 2 - 1 + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1);

        if i < numbers.len() - 1 {
            assert(intersperse_spec(numbers, delimiter)[even(i)] == (intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()])[even(i)]);
            assert(even(i) < intersperse_spec(numbers.drop_last(), delimiter).len());
            assert(intersperse_spec(numbers, delimiter)[even(i)] == intersperse_spec(numbers.drop_last(), delimiter)[even(i)]);
            assert(intersperse_spec(numbers, delimiter)[even(i)] == numbers[i]);
        } else {
            assert(i == numbers.len() - 1);
            assert(intersperse_spec(numbers, delimiter)[even(numbers.len() - 1)] == numbers[numbers.len() - 1]);
        }
    }
}

proof fn lemma_intersperse_spec_delimiter_odd(
    numbers: Seq<u64>,
    delimiter: u64,
    i: int,
)
    requires
        0 <= i < numbers.len() - 1,
    ensures
        intersperse_spec(numbers, delimiter)[odd(i)] == delimiter,
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        assert(false); // Should not reach here due to requires
    } else {
        proof {
            lemma_intersperse_spec_delimiter_odd(numbers.drop_last(), delimiter, i);
        }
        if i < numbers.len() - 2 {
            assert(intersperse_spec(numbers, delimiter)[odd(i)] == intersperse_spec(numbers.drop_last(), delimiter)[odd(i)]);
            assert(intersperse_spec(numbers, delimiter)[odd(i)] == delimiter);
        } else {
            assert(i == numbers.len() - 2);
            assert(intersperse_spec(numbers, delimiter)[odd(numbers.len() - 2)] == delimiter);
        }
    }
}

proof fn lemma_intersperse_quantified_iff_spec(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
    decreases numbers.len(),
{
    if numbers.len() == 0 {
        assert(intersperse_spec(numbers, delimiter).len() == 0);
        assert(intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)));
    } else {
        // Need to cover all indices for len_even and delimiter_odd due to forall
        let len_int = numbers.len() as int;
        assert forall |i:int| 0 <= i < len_int implies #[trigger] intersperse_spec(numbers, delimiter).len() == (if len_int == 0 { 0 } else { 2 * len_int - 1 }) by {
            lemma_intersperse_spec_len_even(numbers, delimiter, i);
        }
        assert forall |i:int| 0 <= i < len_int implies #[trigger] intersperse_spec(numbers, delimiter)[even(i)] == numbers[i] by {
            lemma_intersperse_spec_len_even(numbers, delimiter, i);
        }

        if numbers.len() > 1 {
            assert forall |i:int| 0 <= i < len_int - 1 implies #[trigger] intersperse_spec(numbers, delimiter)[odd(i)] == delimiter by {
                lemma_intersperse_spec_delimiter_odd(numbers, delimiter, i);
            }
        }

        assert(intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)));
    }
}
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: Vec<u64>, delimiter: u64) -> (result: Vec<u64>)
    // post-conditions-start
    ensures
        result@ == intersperse_spec(numbers@, delimiter),
    // post-conditions-end
// </vc-spec>
// <vc-code>
use std::ops::Index;
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: int = 0;

    if numbers.len() == 0 {
        return result;
    }

    // Add first element directly
    result.push(numbers.index(0));
    i = i + 1;

    while i < numbers.len()
        invariant
            0 < i <= numbers.len(),
            result@ == intersperse_spec(numbers@.subsequence(0, i as nat), delimiter),
            intersperse_quantified(numbers@.subsequence(0, i as nat), delimiter, result@),
    {
        // Prove that the current `result@` satisfies the invariant for `numbers@.subsequence(0, i)`
        // This is necessary because after the push operations, `i` increments, and the invariant
        // will apply to the new `i`. Before the push operations, we need to show
        // `result@` for `i` (current) is consistent with `intersperse_spec(numbers@.subsequence(0, i), delimiter)`.
        // This is implicitly true at the beginning of each iteration due to the loop invariant
        // from the previous iteration.

        // Prove that intersperse_spec and intersperse_quantified hold for the current 'i'
        proof {
            lemma_intersperse_quantified_iff_spec(numbers@.subsequence(0, i as nat), delimiter);
        }
        assert(result@ == intersperse_spec(numbers@.subsequence(0, i as nat), delimiter));
        assert(intersperse_quantified(numbers@.subsequence(0, i as nat), delimiter, result@));

        // Add delimiter
        result.push(delimiter);

        // At this point, result@ has intersperse_spec(numbers@.subsequence(0,i), delimiter) + seq![delimiter]
        // Which is `intersperse_spec(numbers@.subsequence(0,i+1), delimiter).drop_last()` if i >= 1
        proof {
            let s_sub_i = numbers@.subsequence(0, i as nat);
            let expected_result_after_delim = intersperse_spec(s_sub_i, delimiter) + seq![delimiter];
            assert(result@ == expected_result_after_delim);

            // We need to prove that the new `result@` (before adding the next number)
            // is consistent with the `intersperse_spec` of the *next* state, or at least
            // that `intersperse_spec(numbers@.subsequence(0, i+1), delimiter)` can be formed from it.
            // By definition:
            // intersperse_spec(S.drop_last(), delimiter) + seq![delimiter, S.last()]
            // Here `S` is `numbers@.subsequence(0, i+1)`.
            // `S.drop_last()` is `numbers@.subsequence(0, i)`.
            // `S.last()` is `numbers@[i]`.
            // So `intersperse_spec(numbers@.subsequence(0, i+1), delimiter)` is
            // `intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter, numbers@[i]]`.
            // Currently, `result@` is `intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter]`.
            // So, after `result.push(numbers.index(i))`, it will become the intended `intersperse_spec` for `i+1`.
        }

        // Add number
        result.push(numbers.index(i));

        // After this, result@ should be intersperse_spec(numbers@.subsequence(0, i+1), delimiter)
        proof {
            let s_sub_i_plus_1 = numbers@.subsequence(0, (i + 1) as nat);
            let expected_next_spec = intersperse_spec(s_sub_i_plus_1, delimiter);
            assert(result@ == expected_next_spec);
            lemma_intersperse_quantified_iff_spec(s_sub_i_plus_1, delimiter);
            assert(intersperse_quantified(s_sub_i_plus_1, delimiter, result@));
        }

        i = i + 1;
    }

    assert(i == numbers.len());
    assert(result@ == intersperse_spec(numbers@, delimiter));
    assert(intersperse_quantified(numbers@, delimiter, result@));

    result
}
// </vc-code>

fn main() {}
}