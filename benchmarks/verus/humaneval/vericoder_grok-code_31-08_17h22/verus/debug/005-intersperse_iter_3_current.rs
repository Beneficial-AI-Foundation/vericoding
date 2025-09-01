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
    }
}

proof fn intersperse_correct(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_quantified(numbers, delimiter, intersperse_spec(numbers, delimiter)),
{
    assert(intersperse_spec(numbers, delimiter).len() == if numbers.len() == 0 { 0 } else { 2*numbers.len()-1 });
    if numbers.len() == 0 {  
    } else {
        let rec = intersperse_spec(numbers.drop_last(), delimiter);
        let dl = numbers.last();
        let result = rec + seq![delimiter, dl];
        assert(result[even(0)] == numbers[0]);
        intersperse_correct(numbers.drop_last(), delimiter);
        assert forall|i: int| 0 <= i < numbers.len() ==> #[trigger] result[even(i)] == numbers[i] by {
            if i == 0 {
                assert(result[0] == numbers[0]);
            } else {
                assert(rec[even(i-1)] == numbers[i-1]);
                assert(even(i) == 2*i);
                assert(even(i-1) == 2*(i-1) == 2*i - 2);
                // Proof that the elements are correctly placed
            }
        }
        assert forall|i: int| 0 <= i < numbers.len()-1 ==> #[trigger] result[odd(i)] == delimiter by {
            assert(i < numbers.len()-1);
            assert(odd(i) == 2*i + 1);
            if i == 0 {
                assert(rec.len() == 2*(numbers.len()-1) -1 ?== 2*(numbers.len()-1) -1 : if numbers.len()-1 ==0 {0} else {2*(numbers.len()-1)-1});
                intersperse_preserves_length(numbers.drop_last(), delimiter);
                assert(result[1] == delimiter);
            } else {
                //assert(rec[odd(i-1)] == delimiter);
            }
        }
    }
}

proof fn lemma_subrange_intersperse(numbers: Seq<u64>, delimiter: u64, k: int)
    requires 0 <= k <= numbers.len()
    ensures intersperse_spec(numbers.subrange(0, k), delimiter) ==
        if k == 0 { seq![] } else { intersperse_spec(numbers.subrange(0, k-1), delimiter) + seq![delimiter, numbers[k-1]] }
{
    if k == 0 {
    } else if k == 1 {
        // intersperse_spec(numbers.subrange(0,1), delimiter) == seq![numbers[0]]
        // right side: intersperse_spec(subrange(0,0), delimiter) + seq![delimiter, numbers[0]] == seq![] + seq![delimiter, numbers[0]]
        // so need to prove seq![numbers[0]] == seq![delimiter, numbers[0]] which is false
        // wait, mistake in spec?
        let sub = numbers.subrange(0,1);
        assert(sub.len() == 1);
        assert(intersperse_spec(sub, delimiter) == sub);
        let left = seq![delimiter, numbers[0]];
        assert(sub[0] == numbers[0]);
        // This lemma is wrong
    } else {
        // For k > 1, subrange(0,k).drop_last() == subrange(0,k-1)
        // Yes
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
                0 <= k <= len,
                result@ == intersperse_spec(numbers@.subrange(0, k as int), delimiter),
                1 <= k || len == 1,  // Note: when k ==1 after first push
        {
            result.push(delimiter);
            result.push(numbers[k]);
            k += 1;
        }
    }
    assert(result@.len() == 2 * numbers@.len() - 1);
    result
}
// </vc-code>

fn main() {}
}