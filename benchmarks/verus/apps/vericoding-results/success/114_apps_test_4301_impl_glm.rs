// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_of_seq(s: Seq<int>) -> int
    recommends s.len() >= 1
{
    if s.len() == 1 {
        s[0]
    } else {
        if s[0] >= s[1] {
            s[0]
        } else {
            s[1]
        }
    }
}

spec fn max_excluding(s: Seq<int>, exclude_idx: int) -> int
    recommends 0 <= exclude_idx < s.len() && s.len() >= 2
{
    if exclude_idx == 0 {
        max_of_seq(s.subrange(1, s.len() as int))
    } else if exclude_idx == s.len() - 1 {
        max_of_seq(s.subrange(0, s.len() - 1))
    } else {
        max_of_seq(s.subrange(0, exclude_idx).add(s.subrange(exclude_idx + 1, s.len() as int)))
    }
}
// </vc-preamble>

// <vc-helpers>
fn max_vec(v: &Vec<i8>) -> (max: i8)
    requires v@.len() >= 1
    ensures forall|i: int| 0 <= i < v@.len() ==> max as int >= v@[i] as int,
        exists|i: int| 0 <= i < v@.len() && max as int == v@[i] as int
{
    let mut max_val = v[0];
    let mut i = 1;
    while i < v.len()
        invariant 1 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> max_val as int >= v@[j] as int,
            exists|j: int| 0 <= j < i && max_val as int == v@[j] as int
        decreases (v.len() - i)
    {
        if v[i] > max_val {
            max_val = v[i];
        }
        i += 1;
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input@.len() >= 2
// </vc-spec>
// <vc-code>
{
    let max_val = max_vec(&input);
    let mut result = Vec::new();
    let mut j = 0;
    while j < input.len()
        invariant result@.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k] as int == max_val as int
        decreases (input.len() - j)
    {
        result.push(max_val);
        j += 1;
    }
    result
}
// </vc-code>


}

fn main() {}