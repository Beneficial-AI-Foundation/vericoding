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
proof fn lemma_find_min_index_preserves_conditions(n: int, packets: Seq<int>, min_index: int)
    requires n >= 2, packets.len() == n, forall|i: int| 0 <= i < packets.len() ==> packets[i] >= 1,
        0 <= min_index < packets.len(), forall|j: int| 0 <= j < packets.len() ==> packets[min_index] <= packets[j],
        forall|k: int| 0 <= k < min_index ==> packets[k] > packets[min_index]
    ensures valid_solution(n, packets, seq![1, min_index + 1])
{
    assert(n >= 2);
    assert(valid_input(n, packets));
    assert(is_possible(n, packets));
    assert(seq![1, min_index + 1].len() == 2);
    assert(seq![1, min_index + 1][0] == 1);
    assert(1 <= min_index + 1 && min_index + 1 <= n);
    assert(exists|i: int| 0 <= i < packets.len() && 
        min_index + 1 == i + 1 &&
        (forall|j: int| 0 <= j < packets.len() ==> packets[i] <= packets[j]) &&
        (forall|k: int| 0 <= k < i ==> packets[k] > packets[i]));
}

spec fn find_min_index(packets: Seq<int>) -> (min_index: int)
    requires packets.len() >= 1
    ensures 0 <= min_index < packets.len(), forall|j: int| 0 <= j < packets.len() ==> packets[min_index] <= packets[j],
        forall|k: int| 0 <= k < min_index ==> packets[k] > packets[min_index]
{
    if packets.len() == 1 {
        0
    } else {
        let prev_min_index = find_min_index(packets.subrange(1, packets.len() as int));
        if packets[0] <= packets[prev_min_index + 1] {
            0
        } else {
            prev_min_index + 1
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, packets: Vec<i8>) -> (result: Vec<i8>)
    requires valid_input(n as int, packets@.map(|i: int, x: i8| x as int))
    ensures valid_solution(n as int, packets@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches and verification */
    let ghost n_int = n as int;
    let ghost packets_seq = packets@.map(|i: int, x: i8| x as int);
    
    if !is_possible(n_int, packets_seq) {
        vec![]
    } else {
        let mut min_index_nat: usize = 0;
        let mut min_value = packets[0];
        
        let mut i: usize = 1;
        while i < n as usize
            invariant
                i <= n as usize,
                min_index_nat < n as usize,
                min_value as int == packets_seq@[min_index_nat as int],
                forall|j: int| 0 <= j < i as int ==> packets_seq@[min_index_nat as int] <= packets_seq@[j],
                forall|k: int| 0 <= k < min_index_nat as int && k < i as int ==> packets_seq@[k] > packets_seq@[min_index_nat as int],
                forall|j: int| 0 <= j < i as int ==> packets_seq@[j] >= min_value as int
            decreases n as usize - i
        {
            let current = packets[i];
            if current < min_value {
                min_value = current;
                min_index_nat = i;
            }
            i += 1;
        }
        
        proof {
            lemma_find_min_index_preserves_conditions(n_int, packets_seq, min_index_nat as int);
        }
        
        vec![1, min_index_nat as i8 + 1]
    }
}
// </vc-code>


}

fn main() {}