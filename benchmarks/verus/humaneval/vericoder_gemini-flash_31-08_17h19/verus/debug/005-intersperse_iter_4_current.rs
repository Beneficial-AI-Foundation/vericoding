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

spec fn even(i: int) -> int {
    2 * i
}

spec fn odd(i: int) -> int {
    2 * i + 1
}

spec fn intersperse_quantified(numbers: Seq<u64>, delimiter: u64, interspersed: Seq<u64>) -> (result:bool) {
    (if numbers.len() == 0 {
        interspersed.len() == 0
    } else {
        interspersed.len() == 2 * numbers.len() - 1
    }) && (forall|i: int| 0 <= i < numbers.len() ==> #[trigger] interspersed[even(i)] == numbers[i])
        && (forall|i: int|
        0 <= i < numbers.len() - 1 ==> #[trigger] interspersed[odd(i)] == delimiter)
}

proof fn lemma_intersperse_spec_len_even(
    numbers: Seq<u64>,
    delimiter: u64,
    i_val: int,
)
    requires
        0 <= i_val < numbers.len(),
    ensures
        intersperse_spec(numbers, delimiter).len() == (if numbers.len() == 0 { 0 } else { 2 * numbers.len() - 1 }),
        intersperse_spec(numbers, delimiter)[even(i_val)] == numbers[i_val],
    decreases numbers.len(),
{
    if numbers.len() == 0 {
        assert(intersperse_spec(numbers, delimiter).len() == 0);
    } else if numbers.len() == 1 {
        assert(intersperse_spec(numbers, delimiter).len() == 1);
        assert(intersperse_spec(numbers, delimiter)[even(0)] == numbers[0]);
    } else {
        proof {
            lemma_intersperse_spec_len_even(numbers.drop_last(), delimiter, i_val);
        }
        assert(intersperse_spec(numbers, delimiter).len() == intersperse_spec(numbers.drop_last(), delimiter).len() + 2);
        assert(intersperse_spec(numbers, delimiter).len() == (2 * (numbers.drop_last()).len() - 1) + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * (numbers.len() - 1) - 1 + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 2 - 1 + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 1);

        if i_val < numbers.len() - 1 {
            assert(intersperse_spec(numbers, delimiter)[even(i_val)] == (intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()])[even(i_val)]);
            assert(even(i_val) < intersperse_spec(numbers.drop_last(), delimiter).len());
            assert(intersperse_spec(numbers, delimiter)[even(i_val)] == intersperse_spec(numbers.drop_last(), delimiter)[even(i_val)]);
            assert(intersperse_spec(numbers, delimiter)[even(i_val)] == numbers[i_val]);
        } else {
            assert(i_val == numbers.len() - 1);
            assert(intersperse_spec(numbers, delimiter)[even(numbers.len() - 1)] == numbers[numbers.len() - 1]);
        }
    }
}

proof fn lemma_intersperse_spec_delimiter_odd(
    numbers: Seq<u64>,
    delimiter: u64,
    i_val: int,
)
    requires
        0 <= i_val < numbers.len() - 1,
    ensures
        intersperse_spec(numbers, delimiter)[odd(i_val)] == delimiter,
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        // Should not reach here due to requires
        assert(false);
    } else {
        if i_val < numbers.len() - 2 {
            proof {
                lemma_intersperse_spec_delimiter_odd(numbers.drop_last(), delimiter, i_val);
            }
            assert(intersperse_spec(numbers, delimiter)[odd(i_val)] == intersperse_spec(numbers.drop_last(), delimiter)[odd(i_val)]);
            assert(intersperse_spec(numbers, delimiter)[odd(i_val)] == delimiter);
        } else {
            assert(i_val == numbers.len() - 2);
            assert(intersperse_spec(numbers, delimiter)[odd(numbers.len() - 2)] == delimiter);
        }
    }
}

proof fn lemma_intersperse_quantified_iff_spec(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
{
    if numbers.len() == 0 {
        assert(intersperse_spec(numbers, delimiter).len() == 0);
        assert(intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)));
    } else {
        let len_int = numbers.len() as int;

        assert forall |i: int| 0 <= i < len_int implies #[trigger] intersperse_spec(numbers, delimiter)[even(i)] == numbers[i] by {
            lemma_intersperse_spec_len_even(numbers, delimiter, i);
        }

        if numbers.len() > 1 {
            assert forall |i: int| 0 <= i < len_int - 1 implies #[trigger] intersperse_spec(numbers, delimiter)[odd(i)] == delimiter by {
                lemma_intersperse_spec_delimiter_odd(numbers, delimiter, i);
            }
        }
        
        let expected_len = if numbers.len() == 0 { 0 } else { 2 * numbers.len() - 1 };
        assert(intersperse_spec(numbers, delimiter).len() == expected_len) by {
            if numbers.len() > 0 {
                lemma_intersperse_spec_len_even(numbers, delimiter, 0); // Any valid index works for length proof
            }
        };

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
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: int = 0;

    if numbers.len() == 0 {
        return result;
    }

    // Add first element directly
    result.push(numbers.index(0));
    i = i + 1;

    // The length of result is now 1.
    // The spec intersperse_spec(numbers@.subsequence(0, 1), delimiter) is just numbers@[0].
    // So result@ == numbers@[0] is true.
    proof {
        assert(i == 1);
        assert(result@ == seq![numbers@.index(0)]);
        assert(intersperse_spec(numbers@.subsequence(0, 1), delimiter) == numbers@.subsequence(0, 1));
        assert(result@ == intersperse_spec(numbers@.subsequence(0, 1), delimiter));
        lemma_intersperse_quantified_iff_spec(numbers@.subsequence(0, 1), delimiter);
        assert(intersperse_quantified(numbers@.subsequence(0, 1), delimiter, result@));

    }

    while i < numbers.len()
        invariant
            0 < i <= numbers.len(),
            result@ == intersperse_spec(numbers@.subsequence(0, i as nat), delimiter),
            intersperse_quantified(numbers@.subsequence(0, i as nat), delimiter, result@),
    {
        // Add delimiter
        result.push(delimiter);
        
        // Assert the state after pushing delimiter
        // The result will be intersperse_spec(numbers@.subsequence(0, i as nat), delimiter) + seq![delimiter]
        proof {
            let s_sub_i = numbers@.subsequence(0, i as nat);
            let current_result_spec = intersperse_spec(s_sub_i, delimiter);
            assert(result@ == current_result_spec + seq![delimiter]);
        }

        // Add number
        result.push(numbers.index(i));

        // After this, result@ should be intersperse_spec(numbers@.subsequence(0, i+1), delimiter)
        proof {
            let s_sub_i_plus_1 = numbers@.subsequence(0, (i + 1) as nat);
            let expected_next_spec = intersperse_spec(s_sub_i_plus_1, delimiter);
            
            // From definition of intersperse_spec:
            // intersperse_spec(S, D) = intersperse_spec(S.drop_last(), D) + seq![D, S.last()]
            // Here S is numbers@.subsequence(0, i+1)
            // S.drop_last() is numbers@.subsequence(0, i)
            // S.last() is numbers@[i]
            // So expected_next_spec is intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter, numbers@[i]]
            // And current result@ is (intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter]) + seq![numbers@[i]]
            // These are equal.
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