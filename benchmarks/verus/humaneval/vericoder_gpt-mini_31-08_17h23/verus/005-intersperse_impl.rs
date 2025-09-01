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
spec fn prefix(numbers: Seq<u64>, k: int) -> Seq<u64>
    requires 0 <= k && k <= numbers.len()
    decreases k
{
    if k == 0 {
        seq![]
    } else {
        prefix(numbers, k - 1) + seq![numbers[k - 1]]
    }
}

proof fn prefix_drop_last(numbers: Seq<u64>, k: int)
    requires 1 <= k && k <= numbers.len()
    ensures prefix(numbers, k).drop_last() == prefix(numbers, k - 1)
{
    if k == 1 {
        // prefix(numbers,1) == seq![numbers[0]] so drop_last == seq![] == prefix(numbers,0)
        assert(prefix(numbers, 1) == seq![numbers[0]]);
        assert(prefix(numbers, 1).drop_last() == seq![]);
        assert(prefix(numbers, 0) == seq![]);
    } else {
        // prefix(numbers,k) == prefix(numbers,k-1) + seq![numbers[k-1]]
        assert(prefix(numbers, k) == prefix(numbers, k - 1) + seq![numbers[k - 1]]);
        // drop_last of that is prefix(numbers,k-1) + seq![numbers[k-1]].drop_last() == prefix(numbers,k-1) + seq![] == prefix(numbers,k-1)
        assert((prefix(numbers, k - 1) + seq![numbers[k - 1]]).drop_last() == prefix(numbers, k - 1));
        assert(prefix(numbers, k).drop_last() == prefix(numbers, k - 1));
    }
}

proof fn prefix_last(numbers: Seq<u64>, k: int)
    requires 1 <= k && k <= numbers.len()
    ensures prefix(numbers, k).last() == numbers[k - 1]
{
    if k == 1 {
        assert(prefix(numbers, 1) == seq![numbers[0]]);
        assert(prefix(numbers, 1).last() == numbers[0]);
    } else {
        // prefix(numbers,k) == prefix(numbers,k-1) + seq![numbers[k-1]]
        assert(prefix(numbers, k) == prefix(numbers, k - 1) + seq![numbers[k - 1]]);
        // last of concatenation equals last element of the added seq
        assert((prefix(numbers, k - 1) + seq![numbers[k - 1]]).last() == numbers[k - 1]);
        assert(prefix(numbers, k).last() == numbers[k - 1]);
    }
}

proof fn intersperse_spec_single(x: u64, delimiter: u64)
    ensures intersperse_spec(seq![x], delimiter) == seq![x]
{
    assert(intersperse_spec(seq![x], delimiter) == seq![x]);
}

proof fn intersperse_spec_append(numbers: Seq<u64>, delimiter: u64, last: u64)
    requires numbers.len() >= 1
    ensures intersperse_spec(numbers + seq![last], delimiter) == intersperse_spec(numbers, delimiter) + seq![delimiter, last]
{
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
    let n: usize = numbers.len();
    let mut res: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant i <= n && res@ == intersperse_spec(prefix(numbers@, (i as int)), delimiter)
        decreases n - i
    {
        let old_seq: Seq<u64> = res@;
        let x: u64 = numbers[i];
        if i == 0 {
            res.push(x);
            proof {
                // From invariant with i == 0
                assert(old_seq == intersperse_spec(prefix(numbers@, 0), delimiter));
                assert(prefix(numbers@, 0) == seq![]);
                assert(intersperse_spec(prefix(numbers@, 0), delimiter) == seq![]);
                // so old_seq == seq![]::<u64>
                assert(old_seq == seq![]::<u64>);
                // After push, res@ == old_seq + seq![x] == seq![x]
                assert(res@ == old_seq + seq![x]);
                assert(res@ == seq![x]);
                // prefix(numbers,1) == seq![numbers[0]] and intersperse_spec(seq![numbers[0]], delimiter) == seq![numbers[0]]
                assert(prefix(numbers@, 1) == seq![numbers@[0]]);
                assert(intersperse_spec(prefix(numbers@, 1), delimiter) == seq![numbers[0]]);
                assert(res@ == intersperse_spec(prefix(numbers@, 1), delimiter));
            }
        } else {
            res.push(delimiter);
            res.push(x);
            proof {
                // Show prefix(numbers, i+1).drop_last() == prefix(numbers, i)
                let k_plus: int = (i + 1) as int;
                let k: int = i as int;
                assert(1 <= k_plus && k_plus <= numbers@.len());
                prefix_drop_last(numbers@, k_plus);
                assert(prefix(numbers@, k_plus).drop_last() == prefix(numbers@, k));
                // last element of prefix(numbers, i+1) is numbers[i]
                prefix_last(numbers@, k_plus);
                assert(prefix(numbers@, k_plus).last() == numbers[k]);
                // Use intersperse_spec definition to expand
                assert(intersperse_spec(prefix(numbers@, k_plus), delimiter) == intersperse_spec(prefix(numbers@, k), delimiter) + seq![delimiter, numbers[k]]);
                // res@ equals old_seq + seq![delimiter, numbers[k]]
                assert(res@ == old_seq + seq![delimiter, numbers[k]]);
                assert(res@ == intersperse_spec(prefix(numbers@, k_plus), delimiter));
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

fn main() {}
}