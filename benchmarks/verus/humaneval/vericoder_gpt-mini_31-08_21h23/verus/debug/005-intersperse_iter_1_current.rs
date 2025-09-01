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
// <vc-helpers>

proof fn intersperse_spec_append_last(s: Seq<u64>, x: u64, delimiter: u64)
    ensures
        intersperse_spec(s + seq![x], delimiter)
            == (if s.len() == 0 {
                    seq![x]
                } else {
                    intersperse_spec(s, delimiter) + seq![delimiter, x]
                }),
    decreases s.len()
{
    if s.len() == 0 {
        // If s is empty, then s + [x] has length 1, so intersperse_spec returns the sequence itself.
        // intersperse_spec(seq![x], delimiter) == seq![x]
    } else {
        // s.len() >= 1, so (s + [x]).len() > 1 and we can apply the recursive case of intersperse_spec.
        // By the spec: intersperse_spec((s + [x])) == intersperse_spec((s + [x]).drop_last()) + seq![delimiter, (s + [x]).last()]
        // But (s + [x]).drop_last() == s and (s + [x]).last() == x, so we conclude the desired equality.
        assert((s + seq![x]).len() > 1);
        // unfold the recursive definition:
        let tmp := intersperse_spec((s + seq![x]).drop_last(), delimiter) + seq![delimiter, (s + seq![x]).last()];
        // simplify using properties of concatenation:
        assert((s + seq![x]).drop_last() == s);
        assert((s + seq![x]).last() == x);
        // therefore intersperse_spec(s + [x]) == intersperse_spec(s) + [delimiter, x]
    }
}

// </vc-helpers>
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
    // impl-start
    let n: usize = numbers.len();
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant result@ == intersperse_spec(numbers@.slice(0, i as nat), delimiter)
    {
        if i > 0 {
            result.push(delimiter);
        }
        result.push(numbers.get(i));
        // Prove the invariant for i+1
        proof {
            let s: Seq<u64> = numbers@.slice(0, i as nat);
            let x_spec: u64 = numbers@[i as int];
            // After pushes, result@ == (old_result@) + (if i==0 then seq![x_spec] else seq![delimiter, x_spec])
            // Use lemma to relate intersperse_spec(s + [x]) to the right-hand side.
            intersperse_spec_append_last(s, x_spec, delimiter);
            // Show that s + seq![x_spec] equals the slice up to i+1
            assert(s + seq![x_spec] == numbers@.slice(0, (i + 1) as nat));
            // Combine to establish the invariant at i+1
            // result@ is equal to intersperse_spec(numbers@.slice(0, i+1), delimiter)
        }
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}