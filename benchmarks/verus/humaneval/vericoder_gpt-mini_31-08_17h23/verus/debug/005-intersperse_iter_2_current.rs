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
proof fn intersperse_spec_single(x: u64, delimiter: u64)
    ensures intersperse_spec(seq![x], delimiter) == seq![x]
{
    // By definition of intersperse_spec: if len <= 1 then returns numbers
    assert(intersperse_spec(seq![x], delimiter) == seq![x]);
}

proof fn intersperse_spec_append(numbers: Seq<u64>, delimiter: u64, last: u64)
    requires numbers.len() >= 1
    ensures intersperse_spec(numbers + seq![last], delimiter) == intersperse_spec(numbers, delimiter) + seq![delimiter, last]
{
    // (numbers + [last]).len() >= 2, so by definition:
    // intersperse_spec(numbers + [last], delimiter) == intersperse_spec((numbers + [last]).drop_last(), delimiter) + seq![delimiter, last]
    assert((numbers + seq![last]).drop_last() == numbers);
    assert(intersperse_spec(numbers + seq![last], delimiter) == intersperse_spec((numbers + seq![last]).drop_last(), delimiter) + seq![delimiter, last]);
    assert(intersperse_spec(numbers + seq![last], delimiter) == intersperse_spec(numbers, delimiter) + seq![delimiter, last]);
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
    // impl-start
    let n: nat = numbers.len();
    let mut res: Vec<u64> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n,
        invariant res@ == intersperse_spec(numbers@.slice(0, i), delimiter)
        decreases n - i
    {
        let old_seq: Seq<u64> = res@;
        let x: u64 = numbers[i];
        if i == 0 {
            res.push(x);
            proof {
                // old_seq == intersperse_spec(numbers@.slice(0,0), delimiter) == seq![]
                assert(old_seq == seq![]);
                // numbers@.slice(0,1).len() <= 1 so intersperse_spec returns the sequence itself
                assert(numbers@.slice(0,1).len() <= 1);
                // res@ == seq![x] and seq![x] == numbers@.slice(0,1)
                assert(res@ == seq![numbers@[0]]);
                assert(intersperse_spec(numbers@.slice(0,1), delimiter) == numbers@.slice(0,1));
                assert(res@ == intersperse_spec(numbers@.slice(0,1), delimiter));
            }
        } else {
            res.push(delimiter);
            res.push(x);
            proof {
                // By invariant, old_seq == intersperse_spec(numbers@.slice(0,i), delimiter)
                // We need to show res@ == intersperse_spec(numbers@.slice(0,i+1), delimiter)
                // Observe that numbers@.slice(0,i+1).drop_last() == numbers@.slice(0,i)
                assert((numbers@.slice(0, i+1)).drop_last() == numbers@.slice(0, i));
                // And its last element is numbers@[i]
                assert((numbers@.slice(0, i+1)).last() == numbers@[i]);
                // Use the lemma / definition to rewrite intersperse_spec for the longer slice
                assert(intersperse_spec(numbers@.slice(0, i+1), delimiter) == intersperse_spec(numbers@.slice(0, i), delimiter) + seq![delimiter, numbers@[i]]);
                // res@ equals old_seq + seq![delimiter, numbers@[i]]
                assert(res@ == old_seq + seq![delimiter, numbers@[i]]);
                // Conclude the invariant for i+1
                assert(res@ == intersperse_spec(numbers@.slice(0, i+1), delimiter));
            }
        }
        i = i + 1;
    }
    // At loop exit i == n, so res@ == intersperse_spec(numbers@.slice(0,n), delimiter) == intersperse_spec(numbers@, delimiter)
    res
    // impl-end
}
// </vc-code>

fn main() {}
}