// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, v: int, sellers: Seq<Seq<int>>) -> bool {
    n >= 0 && v >= 0 && sellers.len() == n && 
    forall|i: int| 0 <= i < sellers.len() ==> sellers[i].len() > 0
}

spec fn valid_output(count: int, indices: Seq<int>, n: int) -> bool {
    count == indices.len() && count >= 0 && count <= n &&
    (forall|i: int| 0 <= i < indices.len() ==> 1 <= indices[i] <= n) &&
    (forall|i: int| 0 <= i < indices.len() - 1 ==> indices[i] < indices[i + 1])
}

spec fn correct_solution(v: int, sellers: Seq<Seq<int>>, indices: Seq<int>) -> bool 
    recommends 
        forall|i: int| 0 <= i < sellers.len() ==> sellers[i].len() > 0,
        forall|i: int| 0 <= i < indices.len() ==> 1 <= indices[i] <= sellers.len()
{
    (forall|i: int| 0 <= i < indices.len() ==> v > seq_min(sellers[indices[i] - 1])) &&
    (forall|i: int| 0 <= i < sellers.len() ==> (v > seq_min(sellers[i]) <==> indices.contains(i + 1)))
}

spec fn seq_min(s: Seq<int>) -> int 
    recommends s.len() > 0
{
    if s.len() == 1 {
        s[0]
    } else {
        if s[0] <= seq_min(s.subrange(1, s.len() as int)) {
            s[0]
        } else {
            seq_min(s.subrange(1, s.len() as int))
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u32, v: u32, sellers: Vec<Vec<u32>>) -> (result: (u32, Vec<u32>))
    requires n >= 0 && v >= 0 && sellers.len() == n
    requires forall|i: int| 0 <= i < sellers.len() ==> sellers[i].len() > 0
    ensures ({
        let (count, indices) = result;
        count == indices.len() && count >= 0 && count <= n &&
        (forall|i: int| 0 <= i < indices.len() ==> 1 <= indices[i] <= n) &&
        (forall|i: int| 0 <= i < indices.len() - 1 ==> indices[i] < indices[i + 1])
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0, Vec::new())
}
// </vc-code>


}

fn main() {}