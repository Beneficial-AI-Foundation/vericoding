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
proof fn intersperse_spec_append(s: Seq<u64>, x: u64, delimiter: u64)
    ensures
        intersperse_spec(s + seq![x], delimiter) ==
            if s.len() == 0 {
                seq![x]
            } else {
                intersperse_spec(s, delimiter) + seq![delimiter, x]
            }
    decreases s.len()
{
    if s.len() == 0 {
        // s + seq![x] has length 1, so intersperse_spec returns the sequence itself
        assert(intersperse_spec(s + seq![x], delimiter) == seq![x]);
    } else {
        // s + seq![x] has length > 1, so by definition:
        // intersperse_spec(s + seq![x], delimiter) ==
        //     intersperse_spec((s + seq![x]).drop_last(), delimiter) + seq![delimiter, (s + seq![x]).last()]
        assert(intersperse_spec(s + seq![x], delimiter) ==
               intersperse_spec((s + seq![x]).drop_last(), delimiter) + seq![delimiter, (s + seq![x]).last()]);
        // But (s + seq![x]).drop_last() == s and (s + seq![x]).last() == x
        assert((s + seq![x]).drop_last() == s);
        assert((s + seq![x]).last() == x);
        // therefore
        assert(intersperse_spec((s + seq![x]).drop_last(), delimiter) == intersperse_spec(s, delimiter));
        assert(intersperse_spec(s + seq![x], delimiter) == intersperse_spec(s, delimiter) + seq![delimiter, x]);
    }
}

fn intersperse_vec_from_seq(s: Seq<u64>, delimiter: u64) -> Vec<u64>
    ensures
        result@ == intersperse_spec(s, delimiter),
    decreases s.len()
{
    if s.len() == 0 {
        Vec::new()
    } else if s.len() == 1 {
        let mut v = Vec::new();
        v.push(s[0]);
        proof {
            assert(v@ == seq![s[0]]);
            assert(v@ == intersperse_spec(s, delimiter));
        }
        v
    } else {
        let mut v = intersperse_vec_from_seq(s.drop_last(), delimiter);
        v.push(delimiter);
        v.push(s.last());
        proof {
            // by induction v@ == intersperse_spec(s.drop_last(), delimiter)
            // and by lemma intersperse_spec_append:
            intersperse_spec_append(s.drop_last(), s.last(), delimiter);
            // since s == s.drop_last() + seq![s.last()] and drop_last length > 0 (because s.len() > 1),
            // intersperse_spec(s, delimiter) == intersperse_spec(s.drop_last(), delimiter) + seq![delimiter, s.last()]
            assert(intersperse_spec(s, delimiter) == intersperse_spec(s.drop_last(), delimiter) + seq![delimiter, s.last()]);
            // pushing delimiter and then last yields that v@ equals that concatenation
            assert(v@ == intersperse_spec(s, delimiter));
        }
        v
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
    intersperse_vec_from_seq(numbers@, delimiter)
}
// </vc-code>

fn main() {}
}