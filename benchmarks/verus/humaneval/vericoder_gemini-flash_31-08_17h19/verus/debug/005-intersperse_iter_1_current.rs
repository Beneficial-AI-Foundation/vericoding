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
        assert(intersperse_spec(numbers, delimiter).len() == (2 * (numbers.drop_last()).len() - 1) + 2);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * (numbers.len() - 1) + 1);
        assert(intersperse_spec(numbers, delimiter).len() == 2 * numbers.len() - 2 + 1);
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
        proof { lemma_intersperse_spec_len_even(numbers, delimiter, 0); } // Prove for all i from this.
        proof { lemma_intersperse_spec_len_even(numbers, delimiter, numbers.len() / 2); }
        proof { lemma_intersperse_spec_len_even(numbers, delimiter, numbers.len() - 1); }

        if numbers.len() > 1 {
            proof { lemma_intersperse_spec_delimiter_odd(numbers, delimiter, 0); } // Prove for all i from this.
            proof { lemma_intersperse_spec_delimiter_odd(numbers, delimiter, (numbers.len() - 2) / 2); }
            proof { lemma_intersperse_spec_delimiter_odd(numbers, delimiter, numbers.len() - 2); }
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
{
    let mut result: Vec<u64> = Vec::new();
    let mut i: int = 0;

    if numbers.len() == 0 {
        return result;
    }

    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result@ == intersperse_spec(numbers@.subsequence(0, i), delimiter),
            intersperse_quantified(numbers@.subsequence(0, i), delimiter, result@),
    {
        if i > 0 {
            result.push(delimiter);
            proof {
                assert(result@.drop_last() == intersperse_spec(numbers@.subsequence(0, i), delimiter).drop_last());
                // The current intersperse_spec for numbers@.subsequence(0, i) is:
                // intersperse_spec(numbers@.subsequence(0, i-1), delimiter) + seq![delimiter, numbers@[i-1]]
                // So, after adding delimiter, it matches the odd position of numbers@[i-1] in the current result.
                // The tricky part is relating the full sequence based on i.
                // The invariant about intersperse_quantified on result@.drop_last() for subsequence (0, i-1) is what we need.

                // Prove that after adding delimiter, the odd property holds for the newly added delimiter
                let prev_i = i - 1;
                let prev_len = numbers@.subsequence(0, prev_i).len();
                let current_len_before_delimiter = result@.len();
                assert(current_len_before_delimiter == (if prev_len == 0 { 0 } else { 2 * prev_len - 1 }));

                assert(odd(prev_i) == 2 * prev_i + 1);
                assert(result@.len() - 1 == current_len_before_delimiter); // This is the old length

                // The new element is at index current_len_before_delimiter.
                // Is this index odd(prev_i)?
                // Target index for new delimiter: odd(prev_i)
                // The actual index of the new delimiter is 2 * (i-1).
                // Example: i=1, numbers.len()=1. result=numbers[0]. i=1. prev_i=0. current_len_before_delimiter=1.
                // We add delimiter. Result: numbers[0], delimiter. index of delimiter is 1. odd(0) is 1. Correct.
                // Example: i=2, numbers.len()=2. result=numbers[0], delimiter, numbers[1].
                // Before loop: result = [numbers[0]]. i = 1.
                // Loop 1: i=1. result = [numbers[0]].
                //   if i > 0 is false.
                //   result.push(numbers[0]). result = [numbers[0]].
                //   i = 1.
                // Next Iteration: i=1. numbers[0].
                //   if i > 0 is true.
                //   result.push(delimiter). result = [numbers[0], delimiter].
                //   assert(result@ == seq![numbers@[0], delimiter]);
                //   assert(intersperse_spec(numbers@.subsequence(0, 1), delimiter) == seq![numbers@[0]]);
                //   ASSERT(result@ == intersperse_spec(numbers@.subsequence(0, 1), delimiter));  // ERROR -- this is where my invariant reasoning breaks.

                // Let's re-evaluate the loop invariant for the `result@ == intersperse_spec(numbers@.subsequence(0, i), delimiter)` part.
                // The current `result` vector is designed to hold the interspersal up to `i` elements from the original `numbers` sequence.

                // When i=0: result is empty, numbers.subsequence(0,0) is empty. Correct.
                // When i=1: we add numbers[0]. result is `seq![numbers[0]]`. numbers.subsequence(0,1) is `seq![numbers[0]]`. Intersperse_spec: `seq![numbers[0]]`. Correct.
                // When i=2: we add delimiter, then numbers[1].
                // Before adding delimiter: result is `seq![numbers[0]]`.
                // After adding delimiter: result is `seq![numbers[0], delimiter]`.
                // After adding numbers[1]: result is `seq![numbers[0], delimiter, numbers[1]]`.
                // intersperse_spec(numbers@.subsequence(0, 2), delimiter) should be `seq![numbers[0], delimiter, numbers[1]]`. Correct.
            }
        }
        result.push(numbers.index(i));
        proof {
            // Prove that the invariant holds after adding numbers.index(i)
            // Let `s_prev` be `intersperse_spec(numbers@.subsequence(0, i), delimiter)`
            // Let `s_curr` be `intersperse_spec(numbers@.subsequence(0, i + 1), delimiter)`

            // Case 1: i == 0
            // result@ (before push num) == empty sequence.
            // result@ (after push num) == seq![numbers@[0]]
            // intersperse_spec(numbers@.subsequence(0, 1), delimiter) == seq![numbers@[0]]
            // Assertion holds.
            if i == 0 {
                assert(result@ == Seq::<u64>::empty());
                result.push(numbers.index(i));
                assert(result@ == seq![numbers@[0]]);
                assert(intersperse_spec(numbers@.subsequence(0, 1), delimiter) == seq![numbers@[0]]);
                assert(result@ == intersperse_spec(numbers@.subsequence(0, 1), delimiter));
            } else {
                // Case 2: i > 0
                // result@ (before push delimiter) == intersperse_spec(numbers@.subsequence(0, i), delimiter)
                // Let s_sub_i = intersperse_spec(numbers@.subsequence(0, i), delimiter)
                // Then result@ (before push num) == s_sub_i + seq![delimiter]
                // This means result@.drop_last() == s_sub_i
                // Also: s_sub_i = intersperse_spec(numbers@.subsequence(0, i-1), delimiter) + seq![delimiter, numbers@[i-1]]
                // So, result@ (before push num) == intersperse_spec(numbers@.subsequence(0, i-1), delimiter) + seq![delimiter, numbers@[i-1], delimiter]
                // This is not what we want.

                // Let's restart the invariant. The result@ should represent the interspersal up to the *current* `i` element being processed.
                // The loop should process `numbers[0]`, then `delimiter, numbers[1]`, then `delimiter, numbers[2]`, etc.

                // Invariant re-evaluation:
                // `result` contains `intersperse_spec(numbers.subsequence(0, i), delimiter)`.
                // `i` is the index of the next number to be added.
                // `result` currently holds the interspersion of `numbers[0..i-1]`.

                // Iteration 0: i=0
                //   Invariant: result@ is empty. intersperse_spec(numbers@.subsequence(0,0), delimiter) is empty. Holds.
                //   result.push(numbers.index(0));
                //   result@ is seq![numbers[0]]
                //   i := 1
                //   Invariant for next iteration: result@ is seq![numbers[0]], intersperse_spec(numbers@.subsequence(0,1), delimiter) is seq![numbers[0]]. Holds.

                // Iteration 1: i=1
                //   Invariant: result@ is seq![numbers[0]], intersperse_spec(numbers@.subsequence(0,1), delimiter) is seq![numbers[0]]. Holds.
                //   if i > 0 (true): result.push(delimiter);
                //     result@ is seq![numbers[0], delimiter]
                //     intersperse_spec(numbers@.subsequence(0,1), delimiter) + seq![delimiter] is seq![numbers[0], delimiter]
                //     Assert(result@ == intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter]);  // This is the intermediate state, not the invariant.
                //   result.push(numbers.index(1));
                //     result@ is seq![numbers[0], delimiter, numbers[1]]
                //     intersperse_spec(numbers@.subsequence(0,2), delimiter) is intersperse_spec(numbers@.subsequence(0,1), delimiter) + seq![delimiter, numbers@[1]]
                //     intersperse_spec(numbers@.subsequence(0,2), delimiter) is seq![numbers[0]] + seq![delimiter, numbers[1]] = seq![numbers[0], delimiter, numbers[1]]
                //     So, result@ == intersperse_spec(numbers@.subsequence(0,2), delimiter). Holds.
                //   i := 2
                //   Invariant for next iteration: result@ is intersperse_spec(numbers@.subsequence(0,2), delimiter). Holds.

                // This logic seems correct. Let `S_prev = numbers@.subsequence(0, i)`.
                // Before `result.push(delimiter)`: `result@ == intersperse_spec(S_prev, delimiter)`.
                // After `result.push(delimiter)`: `result_temp@ == intersperse_spec(S_prev, delimiter) + seq![delimiter]`. This is not `intersperse_spec(numbers@.subsequence(0, i+1), delimiter)`.
                // The invariant should be about `result` at the *end* of the loop, for the `i` that was *just processed*.

                // Let's try to establish the invariant relation more precisely.
                // inv_A: result@ == intersperse_spec(numbers@.subsequence(0, i), delimiter)
                // inv_B: intersperse_quantified(numbers@.subsequence(0, i), delimiter, result@)

                // Before push(delimiter) and push(numbers[i]):
                // `result@` represents `intersperse_spec(numbers@.subsequence(0, i), delimiter)`.

                // After push(delimiter) (if i > 0):
                // `result_with_delim@ = result@ + seq![delimiter]`
                // `result_with_delim@ = intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter]`
                // Length check: `result_with_delim@.len() == (2 * i - 1) + 1 = 2 * i` (assuming i > 0)
                // This corresponds to `2 * (i+1) - 2`. Not directly `intersperse_spec` for `i+1`.

                // After push(numbers[i]):
                // `result_final@ = result_with_delim@ + seq![numbers@[i]]`
                // `result_final@ = intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter, numbers@[i]]`
                // By definition of `intersperse_spec`:
                // `intersperse_spec(numbers@.subsequence(0, i+1), delimiter) == intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter, numbers@[i]]`
                // So, `result_final@ == intersperse_spec(numbers@.subsequence(0, i+1), delimiter)`.
                // This is the loop invariant for the next iteration where `i` becomes `i+1`.

                // Therefore, the invariant should apply to `i+1`:
                // `result@ == intersperse_spec(numbers@.subsequence(0, i+1), delimiter)` (where `i` is the original `i`)

                // So, let's adjust the variables:
                // `j` as the loop counter, `j` from `0` to `numbers.len() - 1`.
                // `i` is the count of elements *processed so far*.

                // Let `i` be the number of elements from `numbers` that have been processed and added to `result`.
                // At the start of the loop iteration `i`, `result` contains `intersperse_spec(numbers@.subsequence(0, i), delimiter)`.

                // The initial state seems fine.
                // The current `i` is the index of the number to be added.
                // So `result@` at the start of the loop is `intersperse_spec(numbers@.subsequence(0, i), delimiter)`.
                // This is correct because `result@` starts as empty, and `intersperse_spec(numbers@.subsequence(0,0), delimiter)` is empty.

                // Inside the loop:
                // if i > 0:
                //   `result.push(delimiter);`
                //   At this point, `result@` is `intersperse_spec(numbers@.subsequence(0, i), delimiter) + seq![delimiter]`.
                //   We need to prove that `intersperse_quantified` holds for `result@` when the next number is added.
                //   This intermediate step needs to be verified.
                //   The `intersperse_spec` (recursive definition) essentially builds up the sequence this way.
                //   `intersperse_spec(S, d) = intersperse_spec(S.drop_last(), d) + seq![d, S.last()]`
                //   Let `S_i = numbers@.subsequence(0, i)`.
                //   Let `S_i_plus_1 = numbers@.subsequence(0, i+1)`.
                //   When `i > 0`, `intersperse_spec(S_i_plus_1, d) = intersperse_spec(S_i, d) + seq![d, numbers@[i]]`.
                //   At the start of the loop, `result@ == intersperse_spec(S_i, d)`.
                //   `result.push(delimiter)` implies `result@` becomes `intersperse_spec(S_i, d) + seq![d]`.
                //   `result.push(numbers.index(i))` implies `result@` becomes `intersperse_spec(S_i, d) + seq![d, numbers@[i]]`,
                //   which is exactly `intersperse_spec(S_i_plus_1, d)`.
                //   So, the loop invariant `result@ == intersperse_spec(numbers@.subsequence(0, i+1_new), delimiter)` holds.

                // The invariant for `intersperse_quantified` needs to be proven based on this.

                let s_current_sub = numbers@.subsequence(0, i); // This is s_i
                let s_next_sub = numbers@.subsequence(0, i+1); // This is s_i_plus_1

                if i > 0 {
                    let s_prev_result = intersperse_spec(s_current_sub, delimiter);
                    assert(result@ == s_prev_result);
                    let len_prev_result = s_prev_result.len();
                    let expected_len_prev = if i == 0 { 0 } else { 2 * i - 1 };
                    assert(len_prev_result == expected_len_prev);
                    // After push(delimiter)
                    let result_after_delim = result@ + seq![delimiter];
                    assert(result_after_delim.len() == len_prev_result + 1);
                    assert(result_after_delim[odd(i-1)] == delimiter); // This is the property for the newly added delimiter
                }
                // After push(numbers.index(i))
                let result_final_seq = result@ + seq![numbers@[i]];
                let expected_spec_seq = intersperse_spec(s_next_sub, delimiter);
                assert(result_final_seq == expected_spec_seq);
                // Also prove intersperse_quantified for the new sequence.
                proof {
                    lemma_intersperse_quantified_iff_spec(s_next_sub, delimiter);
                }
                assert(intersperse_quantified(s_next_sub, delimiter, expected_spec_seq));
            }
        }
        i = i + 1;
    }

    // After the loop, i == numbers.len()
    // The invariant implies:
    // result@ == intersperse_spec(numbers@.subsequence(0, numbers.len()), delimiter)
    // numbers@.subsequence(0, numbers.len()) is just numbers@.
    // So, result@ == intersperse_spec(numbers@, delimiter).
    assert(i == numbers.len()); // This holds because loop condition is `i < numbers.len()`
    assert(result@ == intersperse_spec(numbers@, delimiter)); // From invariant
    assert(intersperse_quantified(numbers@, delimiter, result@));

    result
}
// </vc-code>

fn main() {}
}