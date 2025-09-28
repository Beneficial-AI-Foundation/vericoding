// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.subrange(1, s.len() as int))
    }
}

spec fn is_distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
}

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i + 1]
}

spec fn is_valid_combination(combo: Seq<int>, k: int, n: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= #[trigger] combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo)
}

spec fn is_valid_extension(temp: Seq<int>, combo: Seq<int>, k: int, n: int, start: int) -> bool {
    combo.len() == k &&
    sum(combo) == n &&
    (forall|j: int| 0 <= j < combo.len() ==> 1 <= #[trigger] combo[j] <= 9) &&
    is_distinct(combo) &&
    is_sorted(combo) &&
    combo.len() >= temp.len() &&
    (forall|i: int| 0 <= i < temp.len() ==> #[trigger] temp[i] == #[trigger] combo[i]) &&
    (forall|i: int| temp.len() <= i < combo.len() ==> #[trigger] combo[i] >= start)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn to_int_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i: int, x: i8| x as int)
}
// </vc-helpers>

// <vc-spec>
fn combination_sum3(k: i8, n: i8) -> (result: Vec<Vec<i8>>)
    requires k > 0 && n > 0 && k <= 9
    ensures 
        (forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == k as int) &&
        (forall|i: int| 0 <= i < result.len() ==> sum(to_int_seq(#[trigger] result[i])) == n as int) &&
        (forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < #[trigger] result[i].len() ==> 1 <= #[trigger] result[i][j] as int <= 9) &&
        (forall|i: int| 0 <= i < result.len() ==> is_distinct(to_int_seq(#[trigger] result[i]))) &&
        (forall|i: int| 0 <= i < result.len() ==> is_sorted(to_int_seq(#[trigger] result[i]))) &&
        (forall|i: int, j: int| 0 <= i < j < result.len() ==> to_int_seq(#[trigger] result[i]) != to_int_seq(#[trigger] result[j])) &&
        (forall|combo: Seq<int>| is_valid_combination(combo, k as int, n as int) ==> exists|i: int| 0 <= i < result.len() && to_int_seq(#[trigger] result[i]) == combo) &&
        (forall|i: int| 0 <= i < result.len() ==> is_valid_combination(to_int_seq(#[trigger] result[i]), k as int, n as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use i64 counters and cast to spec int in invariants and proofs */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut mask: i64 = 0;
    while mask < 512
        invariant
            0 <= mask,
            mask <= 512,
        decreases
            512 - mask
    {
        let mut cnt: i64 = 0;
        let mut ssum: i64 = 0;
        let mut temp: Vec<i8> = Vec::new();
        let mut rem: i64 = mask;
        let mut pos: i64 = 1;
        while pos <= 9
            invariant
                1 <= pos,
                pos <= 10,
                0 <= rem,
                rem <= 512,
                0 <= cnt,
                cnt <= 9,
                temp.len() as i64 == cnt,
                ssum as int == sum(to_int_seq(#[trigger] temp)),
                (forall|i: int| 0 <= i < temp.len() as int ==> 1 <= (temp@[i] as int) && (temp@[i] as int) <= 9),
                (forall|i: int| 0 <= i < temp.len() as int - 1 ==> (temp@[i] as int) < (temp@[i+1] as int)),
            decreases
                10 - pos
        {
            if rem % 2 == 1 {
                temp.push(pos as i8);
                cnt = cnt + 1;
                ssum = ssum + pos;
            }
            rem = rem / 2;
            pos = pos + 1;
        }
        if cnt == k as i64 && ssum == n as i64 {
            proof {
                assert(temp.len() as i64 == k as i64);
                assert(sum(to_int_seq(#[trigger] temp)) == n as int);
                assert((forall|i: int| 0 <= i < temp.len() as int ==> 1 <= (temp@[i] as int) && (temp@[i] as int) <= 9));
                assert((forall|i: int| 0 <= i < temp.len() as int - 1 ==> (temp@[i] as int) < (temp@[i+1] as int)));
                assert(is_distinct(to_int_seq(#[trigger] temp)));
                assert(is_sorted(to_int_seq(#[trigger] temp)));
            }
            result.push(temp);
        }
        mask = mask + 1;
    }
    result
}
// </vc-code>


}

fn main() {}