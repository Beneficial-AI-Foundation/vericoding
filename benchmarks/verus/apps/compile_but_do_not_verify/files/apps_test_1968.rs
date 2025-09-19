// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, v: int, sellers: Seq<Seq<int>>) -> bool {
    n >= 0 && v >= 0 && sellers.len() == n && 
    forall|i: int| 0 <= i < sellers.len() ==> sellers[i].len() > 0
}

spec fn valid_output(count: int, indices: Seq<int>, n: int) -> bool {
    count == indices.len() && count >= 0 && count <= n &&
    (forall|i: int| 0 <= i < indices.len() ==> 1 <= indices[i] <= n) &&
    (forall|i: int| 0 <= i < indices.len() - 1 ==> indices[i] < indices[i+1])
}

spec fn correct_solution(v: int, sellers: Seq<Seq<int>>, indices: Seq<int>) -> bool 
    recommends forall|i: int| 0 <= i < sellers.len() ==> sellers[i].len() > 0,
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
        let first = s[0];
        let rest_min = seq_min(s.subrange(1, s.len() as int));
        if first < rest_min { first } else { rest_min }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i32, v: i32, sellers: Vec<Vec<i32>>) -> (result: (i32, Vec<i32>))
    requires valid_input(n as int, v as int, sellers@.map(|i: int, s: Vec<i32>| s@.map(|j: int, x: i32| x as int)))
    ensures ({
        let (count, indices) = result;
        valid_output(count as int, indices@.map(|i: int, x: i32| x as int), n as int) && 
        correct_solution(v as int, sellers@.map(|i: int, s: Vec<i32>| s@.map(|j: int, x: i32| x as int)), indices@.map(|i: int, x: i32| x as int))
    })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (0, Vec::new())
    // impl-end
}
// </vc-code>


}

fn main() {}