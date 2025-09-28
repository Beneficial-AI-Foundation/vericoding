// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(numbers: Seq<int>, threshold: int) -> bool {
    true
}

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

spec fn has_close_elements(numbers: Seq<int>, threshold: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < numbers.len() && abs_diff(numbers[i], numbers[j]) < threshold
}

spec fn seq_map_to_int(numbers: Seq<i8>) -> Seq<int> {
        numbers.map(|_i: int, x: i8| x as int)
}
    

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma about seq_map_to_int indexing correctness and length preservation */
proof fn lemma_seq_map_to_int_index(numbers: Seq<i8>, k: int)
    requires
        0 <= k < numbers.len(),
    ensures
        seq_map_to_int(numbers)[k] == numbers[k] as int,
{
    assert(seq_map_to_int(numbers)[k] == numbers.map(|_i: int, x: i8| x as int)[k]);
    assert(numbers.map(|_i: int, x: i8| x as int)[k] == numbers[k] as int);
}

/* helper modified by LLM (iteration 5): length of seq_map_to_int equals original length */
proof fn lemma_seq_map_to_int_len(numbers: Seq<i8>)
    ensures
        seq_map_to_int(numbers).len() == numbers.len(),
{
    assert(seq_map_to_int(numbers).len() == numbers.map(|_i: int, x: i8| x as int).len());
    assert(numbers.map(|_i: int, x: i8| x as int).len() == numbers.len());
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Vec<i8>, threshold: i8) -> (result: bool)
    requires valid_input(seq_map_to_int(numbers@), threshold as int)
    ensures result == has_close_elements(seq_map_to_int(numbers@), threshold as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement nested search with robust invariants and indexing proofs */
    let n: usize = numbers.len();
    let mut found: bool = false;
    let mut i: usize = 0;

    while i < n
        invariant
            n == numbers.len(),
            i <= n,
            (!found) || exists|ii: int, jj: int|
                0 <= ii && ii < jj && jj < n as int &&
                abs_diff(seq_map_to_int(numbers@)[ii], seq_map_to_int(numbers@)[jj]) < threshold as int,
            forall|i0: int, j0: int|
                0 <= i0 && i0 < j0 && j0 < n as int &&
                i0 < i as int &&
                abs_diff(seq_map_to_int(numbers@)[i0], seq_map_to_int(numbers@)[j0]) < threshold as int
                ==> found,
        decreases (n - i) as int
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                n == numbers.len(),
                i < n,
                j <= n,
                j >= i + 1,
                (!found) || exists|ii: int, jj: int|
                    0 <= ii && ii < jj && jj < n as int &&
                    abs_diff(seq_map_to_int(numbers@)[ii], seq_map_to_int(numbers@)[jj]) < threshold as int,
                forall|i0: int, j0: int|
                    0 <= i0 && i0 < j0 && j0 < n as int &&
                    (i0 < i as int || (i0 == i as int && j0 < j as int)) &&
                    abs_diff(seq_map_to_int(numbers@)[i0], seq_map_to_int(numbers@)[j0]) < threshold as int
                    ==> found,
            decreases (n - j) as int
        {
            let ai32: i32 = numbers[i] as i32;
            let aj32: i32 = numbers[j] as i32;
            let diff: i32 = if ai32 >= aj32 { ai32 - aj32 } else { aj32 - ai32 };
            let cond: bool = diff < (threshold as i32);

            proof {
                // bounds for indexing in specs
                assert(0 <= i as int && i as int < n as int);
                assert(0 <= j as int && j as int < n as int);
                assert(n as int == numbers@.len());
                lemma_seq_map_to_int_index(numbers@, i as int);
                lemma_seq_map_to_int_index(numbers@, j as int);

                // Relate abs_diff on seq values to arithmetic on ai32/aj32
                assert(seq_map_to_int(numbers@)[i as int] == numbers@[i as int] as int);
                assert(seq_map_to_int(numbers@)[j as int] == numbers@[j as int] as int);
                assert((ai32 as int) == (numbers@[i as int] as int));
                assert((aj32 as int) == (numbers@[j as int] as int));
                assert(((threshold as i32) as int) == (threshold as int));

                if ai32 >= aj32 {
                    assert((ai32 as int) >= (aj32 as int));
                    assert(abs_diff(numbers@[i as int] as int, numbers@[j as int] as int)
                           == (numbers@[i as int] as int) - (numbers@[j as int] as int));
                    assert(abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int])
                           == ((ai32 as int) - (aj32 as int)));
                    assert(((ai32 - aj32) as int) == ((ai32 as int) - (aj32 as int)));
                    if cond {
                        assert(((ai32 - aj32) as int) < (threshold as int));
                        assert(abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int]) < threshold as int);
                    }
                    if abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int]) < threshold as int {
                        assert(((ai32 - aj32) as int) < (threshold as int));
                        assert((ai32 - aj32) < (threshold as i32));
                    }
                } else {
                    assert((aj32 as int) >= (ai32 as int));
                    assert(abs_diff(numbers@[i as int] as int, numbers@[j as int] as int)
                           == (numbers@[j as int] as int) - (numbers@[i as int] as int));
                    assert(abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int])
                           == ((aj32 as int) - (ai32 as int)));
                    assert(((aj32 - ai32) as int) == ((aj32 as int) - (ai32 as int)));
                    if cond {
                        assert(((aj32 - ai32) as int) < (threshold as int));
                        assert(abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int]) < threshold as int);
                    }
                    if abs_diff(seq_map_to_int(numbers@)[i as int], seq_map_to_int(numbers@)[j as int]) < threshold as int {
                        assert(((aj32 - ai32) as int) < (threshold as int));
                        assert((aj32 - ai32) < (threshold as i32));
                    }
                }
            }

            found = found || cond;
            j = j + 1;
        }
        i = i + 1;
    }
    found
}
// </vc-code>


}

fn main() {}