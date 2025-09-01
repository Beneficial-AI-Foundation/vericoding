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
proof fn intersperse_spec_equiv(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_spec(numbers, delimiter) == if numbers.len() == 0 {
            seq![]
        } else if numbers.len() == 1 {
            seq![numbers[0]]
        } else {
            intersperse_spec(numbers.take(numbers.len() - 1), delimiter) + seq![delimiter, numbers[numbers.len() - 1]]
        },
    decreases numbers.len(),
{
    if numbers.len() <= 1 {
        // Base case follows from definition
    } else {
        assert(numbers.drop_last() == numbers.take(numbers.len() - 1));
        assert(numbers.last() == numbers[numbers.len() - 1]);
    }
}

proof fn intersperse_spec_len(numbers: Seq<u64>, delimiter: u64)
    ensures
        intersperse_spec(numbers, delimiter).len() == if numbers.len() == 0 {
            0
        } else {
            2 * numbers.len() - 1
        },
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else if numbers.len() == 1 {
    } else {
        intersperse_spec_len(numbers.drop_last(), delimiter);
        assert(numbers.drop_last().len() == numbers.len() - 1);
    }
}

proof fn intersperse_spec_prefix(numbers: Seq<u64>, delimiter: u64, k: int)
    requires
        0 <= k <= numbers.len(),
    ensures
        intersperse_spec(numbers.take(k), delimiter) == intersperse_spec(numbers, delimiter).take(
            if k == 0 { 0 } else { 2 * k - 1 }
        ),
    decreases numbers.len(),
{
    if k == 0 {
        assert(numbers.take(0) == Seq::<u64>::empty());
        assert(intersperse_spec(Seq::<u64>::empty(), delimiter) == Seq::<u64>::empty());
    } else if k == numbers.len() {
        assert(numbers.take(k) == numbers);
        intersperse_spec_len(numbers, delimiter);
    } else if numbers.len() <= 1 {
        assert(k <= 1);
        if k == 0 {
            assert(numbers.take(0) == Seq::<u64>::empty());
        } else {
            assert(k == 1);
            assert(numbers.len() == 1);
            assert(numbers.take(1) == numbers);
        }
    } else {
        if k < numbers.len() {
            intersperse_spec_prefix(numbers.drop_last(), delimiter, k);
            assert(numbers.drop_last().take(k) == numbers.take(k));
            intersperse_spec_len(numbers.drop_last(), delimiter);
            intersperse_spec_len(numbers.take(k), delimiter);
            let result_full = intersperse_spec(numbers, delimiter);
            let result_prefix = intersperse_spec(numbers.take(k), delimiter);
            assert(result_full == intersperse_spec(numbers.drop_last(), delimiter) + seq![delimiter, numbers.last()]);
            if k == 0 {
            } else {
                assert(result_full.take(2 * k - 1) == intersperse_spec(numbers.drop_last(), delimiter).take(2 * k - 1));
            }
        }
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
    let mut result = Vec::new();
    let n = numbers.len();
    
    if n == 0 {
        return result;
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == if i == 0 { 0 } else { 2 * i - 1 },
            result@ == intersperse_spec(numbers@.take(i as int), delimiter),
        decreases n - i,
    {
        proof {
            intersperse_spec_prefix(numbers@, delimiter, i as int);
            intersperse_spec_prefix(numbers@, delimiter, (i + 1) as int);
            intersperse_spec_len(numbers@.take(i as int), delimiter);
            intersperse_spec_len(numbers@.take((i + 1) as int), delimiter);
        }
        
        if i > 0 {
            result.push(delimiter);
            assert(result@.take((result.len() - 1) as int) == intersperse_spec(numbers@.take(i as int), delimiter));
        }
        
        result.push(numbers[i]);
        
        proof {
            assert(numbers@.take((i + 1) as int).drop_last() == numbers@.take(i as int));
            assert(numbers@.take((i + 1) as int).last() == numbers@[i as int]);
            intersperse_spec_equiv(numbers@.take((i + 1) as int), delimiter);
        }
        
        if i == 0 {
            assert(result@ == seq![numbers@[0]]);
            assert(intersperse_spec(numbers@.take(1), delimiter) == seq![numbers@[0]]);
        } else {
            assert(result@ == intersperse_spec(numbers@.take(i as int), delimiter) + seq![delimiter, numbers@[i as int]]);
        }
        
        i = i + 1;
    }
    
    assert(numbers@.take(n as int) == numbers@);
    result
}
// </vc-code>

fn main() {}
}