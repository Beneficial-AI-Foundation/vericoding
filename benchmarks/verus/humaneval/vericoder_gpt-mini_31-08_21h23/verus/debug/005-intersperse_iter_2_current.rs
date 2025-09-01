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
        // s + [x] has length 1, so by definition intersperse_spec(...) == seq![x]
        assert(intersperse_spec(s + seq![x], delimiter) == seq![x]);
    } else {
        // Use the recursive definition on (s + [x]) which has length > 1
        assert((s + seq![x]).len() > 1);
        assert(intersperse_spec(s + seq![x], delimiter)
            == intersperse_spec((s + seq![x]).drop_last(), delimiter) + seq![delimiter, (s + seq![x]).last()]);
        // Simplify drop_last and last
        assert((s + seq![x]).drop_last() == s);
        assert((s + seq![x]).last() == x);
        // Conclude the desired equality
        assert(intersperse_spec(s + seq![x], delimiter) == intersperse_spec(s, delimiter) + seq![delimiter, x]);
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
    let n: usize = numbers.len();
    let mut result: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant result@ == intersperse_spec(numbers@.slice(0, i as nat), delimiter)
    {
        // Prove what the result will be after pushing the next element(s)
        proof {
            let s: Seq<u64> = numbers@.slice(0, i as nat);
            let x_spec: u64 = numbers@[i as int];
            let old: Seq<u64> = result@;
            // Relate intersperse_spec(s + [x]) to the desired form
            intersperse_spec_append_last(s, x_spec, delimiter);
            assert(s + seq![x_spec] == numbers@.slice(0, (i + 1) as nat));
            if i == 0 {
                assert(old + seq![x_spec] == intersperse_spec(numbers@.slice(0, (i + 1) as nat), delimiter));
            } else {
                assert(old + seq![delimiter, x_spec] == intersperse_spec(numbers@.slice(0, (i + 1) as nat), delimiter));
            }
        }
        if i > 0 {
            result.push(delimiter);
        }
        result.push(numbers.get(i));
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}