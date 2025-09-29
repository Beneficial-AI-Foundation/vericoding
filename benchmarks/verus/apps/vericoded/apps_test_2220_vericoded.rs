// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, k: int, emotes: Seq<int>) -> bool {
    n >= 2 && k >= 1 && m >= 1 && emotes.len() == n &&
    forall|i: int| 0 <= i < emotes.len() ==> emotes[i] >= 1
}

spec fn max_happiness(n: int, m: int, k: int, emotes: Seq<int>) -> int {
    let k_plus_1 = k + 1;
    let total = m / k_plus_1;
    let remainder = m % k_plus_1;

    let max_val = max_value(emotes);
    let second_max_val = second_max_value(emotes);
    remainder * max_val + max_val * (total * k) + second_max_val * total
}

spec fn max_value(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        s[0]
    } else if s.len() > 1 && s[0] >= max_value(s.skip(1)) {
        s[0]
    } else if s.len() > 1 {
        max_value(s.skip(1))
    } else {
        s[0]
    }
}

spec fn second_max_value(s: Seq<int>) -> int {
    let max_val = max_value(s);
    let filtered = filter_out(s, max_val, 1);
    if filtered.len() > 0 {
        max_value(filtered)
    } else {
        1
    }
}

spec fn filter_out(s: Seq<int>, val: int, count: int) -> Seq<int>
    decreases s.len(), count
{
    if s.len() == 0 || count == 0 {
        s
    } else if s[0] == val {
        filter_out(s.skip(1), val, count - 1)
    } else {
        seq![s[0]].add(filter_out(s.skip(1), val, count))
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8, emotes: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, k as int, 
            seq![].add(emotes@.map(|i: int, x: i8| x as int)))
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    0
}
// </vc-code>


}

fn main() {}