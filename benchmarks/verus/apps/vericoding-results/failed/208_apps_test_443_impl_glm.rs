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
/* helper modified by LLM (iteration 5): fixed invariant by breaking chained comparison and using commas */
fn find_first_min_index(packets: &Vec<i8>) -> (index: usize)
    requires packets.len() >= 1
    ensures 
        index < packets.len() && 
        forall|j: int| 0 <= j < packets@.len() ==> packets@[index as int] <= packets@[j] &&
        forall|k: int| 0 <= k < index as int ==> packets@[k] > packets@[index as int]
{
    let mut min_value = packets[0];
    let mut min_index = 0;
    let mut i = 1;
    while i < packets.len()
        invariant
            0 <= min_index as int,
            min_index as int < i as int,
            forall|j: int| 0 <= j < i as int ==> packets@[min_index as int] <= packets@[j],
            forall|k: int| 0 <= k < min_index as int ==> packets@[k] > packets@[min_index as int],
        decreases packets.len() - i
    {
        if packets[i] < min_value {
            min_value = packets[i];
            min_index = i;
        }
        i += 1;
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
/* code modified by LLM (iteration 5): unchanged as helper was fixed */
{
    if n < 2 {
        Vec::new()
    } else if n == 2 && packets[0] == packets[1] {
        Vec::new()
    } else {
        let index = find_first_min_index(&packets);
        vec![1, (index + 1) as i8]
    }
}
// </vc-code>


}

fn main() {}