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
use vstd::*;
  
proof fn intersperse_preserves_length(numbers: Seq<u64>, delimiter: u64)
    decreases numbers.len()
    ensures
        if numbers.len() == 0 {
            true
        } else {
            (intersperse_spec(numbers, delimiter)).len() == 2 * numbers.len() - 1
        },
{
    if numbers.len() == 0 {
    } else {
        intersperse_preserves_length(numbers.drop_last(), delimiter);
        let temp = intersperse_spec(numbers.drop_last(), delimiter);
        assert(temp.len() == 2 * (numbers.len() - 1) - 1);
        assert(intersperse_spec(numbers, delimiter) == temp + seq![delimiter, numbers.last()]);
        assert((temp + seq![delimiter, numbers.last()]).len() == temp.len() + 2);
        assert(temp.len() + 2 == 2 * (numbers.len() - 1) - 1 + 2);
        assert(2 * (numbers.len() - 1) - 1 + 2 == 2 * numbers.len() - 1);
    }
}

proof fn lemma_subrange_intersperse(numbers: Seq<u64>, delimiter: u64, k: int)
    requires 0 <= k <= numbers.len()
    ensures intersperse_spec(numbers.subrange(0, k), delimiter) ==
        if k == 0 { seq![] } else if k == 1 { seq![numbers[0]] } else { intersperse_spec(numbers.subrange(0, k-1), delimiter) + seq![delimiter, numbers[k-1]] }
{
    if k == 0 {
    } else if k == 1 {
        let sub = numbers.subrange(0,1);
        assert(sub.len() == 1);
        assert(intersperse_spec(sub, delimiter) == sub);
        assert(sub == seq![numbers[0]]);
    } else {
        lemma_subrange_intersperse(numbers, delimiter, k-1);
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
    if numbers.len() == 0 {
        return Vec::new();
    }
    let len: usize = numbers.len();
    let cap = 2 * len - (if len > 0 { 1 } else { 0 });
    let mut result = Vec::with_capacity(cap);
    result.push(numbers[0]);
    if numbers.len() > 1 {
        let mut k: usize = 1;
        while k < len
            invariant
                0 < k <= len,
                result@ == intersperse_spec(numbers@.subrange(0, k as int), delimiter),
                1 <= k || len == 1,  // Note: when k ==1 after first push
        {
            result.push(delimiter);
            result.push(numbers[k]);
            k += 1;
            proof { lemma_subrange_intersperse(numbers@, delimiter, k as int); }
        }
    }
    assert(result@.len() == if numbers@.len() == 0 { 0 } else { 2 * numbers@.len() - 1 });
    result
}
// </vc-code>

fn main() {}
}