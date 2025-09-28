// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, packets: Seq<int>) -> bool {
    n >= 1 && packets.len() == n && forall|i: int| 0 <= i < packets.len() ==> packets[i] >= 1
}

spec fn is_possible(n: int, packets: Seq<int>) -> bool
    recommends valid_input(n, packets)
{
    n >= 2 && (n > 2 || packets[0] != packets[1])
}

spec fn sum_packets(packets: Seq<int>) -> int
    decreases packets.len()
{
    if packets.len() == 0 {
        0
    } else {
        packets[0] + sum_packets(packets.subrange(1, packets.len() as int))
    }
}

spec fn valid_solution(n: int, packets: Seq<int>, result: Seq<int>) -> bool
    recommends valid_input(n, packets)
{
    if !is_possible(n, packets) {
        result.len() == 0
    } else {
        result.len() == 2 && result[0] == 1 && 1 <= result[1] <= n &&
        exists|min_index: int| 0 <= min_index < packets.len() && 
        result[1] == min_index + 1 &&
        (forall|j: int| 0 <= j < packets.len() ==> #[trigger] packets[min_index] <= packets[j]) &&
        (forall|k: int| 0 <= k < min_index ==> #[trigger] packets[k] > packets[min_index])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no changes, re-submitting correct helper */
fn find_first_min_index(packets: &Vec<i8>) -> (min_index: usize)
    requires
        packets.len() >= 1,
        forall |i: int| 0 <= i < packets.len() ==> (packets@[i] as int) >= 1,
    ensures
        0 <= min_index < packets.len(),
        ({
            let min_idx = min_index as int;
            let spec_packets = packets@.map(|_i: int, p: i8| p as int);
            (forall |j: int| 0 <= j < spec_packets.len() ==> #[trigger] spec_packets[min_idx] <= spec_packets[j]) &&
            (forall |k: int| 0 <= k < min_idx ==> #[trigger] spec_packets[k] > spec_packets[min_idx])
        }),
{
    let mut min_index: usize = 0;
    let mut i: usize = 1;
    let ghost start_packets = packets@;

    while i < packets.len()
        invariant
            1 <= i <= packets.len(),
            0 <= min_index < i,
            packets@ === start_packets,
            ({
                let min_idx = min_index as int;
                let spec_packets = start_packets.map(|_i: int, p: i8| p as int);
                (forall |j: int| 0 <= j < i ==> #[trigger] spec_packets[min_idx] <= spec_packets[j]) &&
                (forall |k: int| 0 <= k < min_idx ==> #[trigger] spec_packets[k] > spec_packets[min_idx])
            }),
        decreases packets.len() - i
    {
        if packets[i] < packets[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    min_index
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, packets: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, packets@.map(|i: int, x: i8| x as int))
    ensures valid_solution(n as int, packets@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): using spec function in if and adding proof block */
{
    let spec_packets = packets@.map(|_i: int, x: i8| x as int);

    if !is_possible(n as int, spec_packets) {
        return Vec::new();
    } else {
        // Preconditions for find_first_min_index are met here:
        // 1. is_possible ==> n >= 2. requires(valid_input) ==> packets.len() == n.
        //    So packets.len() >= 2, which implies packets.len() >= 1.
        // 2. requires(valid_input) ==> forall packets have value >= 1.
        let min_index = find_first_min_index(&packets);

        let mut res = Vec::new();
        res.push(1i8);
        res.push((min_index + 1) as i8);
        
        proof {
            // The context here is sufficient for Verus to prove the postcondition.
            // - `is_possible` is true.
            // - The postconditions of `find_first_min_index` hold for `min_index`.
            // These facts are sufficient to prove `valid_solution` holds for `res`.
            assert(valid_solution(n as int, spec_packets, res@.map(|i,p|p as int)));
        }
        
        return res;
    }
}
// </vc-code>


}

fn main() {}