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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, packets: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, packets@.map(|i: int, x: i8| x as int))
    ensures valid_solution(n as int, packets@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added explicit witness for existential in postcondition */
    if n < 2 {
        return Vec::new();
    }
    
    if n == 2 {
        if packets[0] == packets[1] {
            return Vec::new();
        }
    }
    
    let mut min_val: i8 = packets[0];
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < n as usize
        invariant
            1 <= i <= n,
            n == packets.len(),
            0 <= min_idx < i,
            min_val == packets[min_idx as int],
            forall|j: int| 0 <= j < i ==> packets@[min_idx as int] as int <= packets@[j] as int,
            forall|k: int| 0 <= k < min_idx ==> packets@[k] as int > packets@[min_idx as int] as int,
        decreases n as int - i as int
    {
        if packets[i] < min_val {
            min_val = packets[i];
            min_idx = i;
        }
        i = i + 1;
    }
    
    let mut result = Vec::new();
    result.push(1i8);
    result.push((min_idx + 1) as i8);
    
    assert(result@.len() == 2);
    assert(result@[0] == 1);
    assert(1 <= result@[1] <= n);
    assert(0 <= min_idx < packets@.len());
    assert(result@[1] == min_idx + 1);
    assert(forall|j: int| 0 <= j < packets@.len() ==> packets@[min_idx as int] as int <= packets@[j] as int);
    assert(forall|k: int| 0 <= k < min_idx ==> packets@[k] as int > packets@[min_idx as int] as int);
    
    // Establish the existential
    assert(exists|min_index: int| 0 <= min_index < packets@.len() && 
        result@[1] == min_index + 1 &&
        (forall|j: int| 0 <= j < packets@.len() ==> #[trigger] packets@[min_index] as int <= packets@[j] as int) &&
        (forall|k: int| 0 <= k < min_index ==> #[trigger] packets@[k] as int > packets@[min_index] as int)) by {
        assert(0 <= min_idx < packets@.len() && 
            result@[1] == min_idx + 1 &&
            (forall|j: int| 0 <= j < packets@.len() ==> packets@[min_idx as int] as int <= packets@[j] as int) &&
            (forall|k: int| 0 <= k < min_idx ==> packets@[k] as int > packets@[min_idx as int] as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}