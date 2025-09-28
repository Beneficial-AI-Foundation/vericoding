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
/* helper modified by LLM (iteration 5): relate Vec mapping to sequence indexing */
proof fn vec_map_index(v: Vec<i8>, i: int)
    requires 0 <= i < v@.len(),
    ensures v@.map(|_, x: i8| x as int)[i] == (v@)[i] as int,
{
    proof {
        let s = v@;
        let mapped = s.map(|_, x: i8| x as int);
        assert(mapped[i] == (s[i] as int));
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
    /* code modified by LLM (iteration 5): check impossibility and find first minimal index */
    let ghost n_int: int = n as int;
    let ghost seq: Seq<int> = packets@.map(|_, x: i8| x as int);
    if packets.len() < 2 || (packets.len() == 2 && packets[0] == packets[1]) {
        let mut res: Vec<i8> = Vec::new();
        proof {
            assert(!is_possible(n_int, seq));
            assert(res@.len() == 0);
        }
        return res;
    }
    let len = packets.len();
    let mut min_index_usize: usize = 0;
    let mut i_usize: usize = 1;
    let ghost mut min_index_g: int = 0;
    let ghost mut i_g: int = 1;
    while i_usize < len
        invariant
            0 <= min_index_g && min_index_g < n_int,
            1 <= i_g && i_g <= n_int,
            min_index_g == (min_index_usize as int),
            i_g == (i_usize as int),
            forall|j: int| 0 <= j < i_g ==> seq[min_index_g] <= seq[j],
        decreases n_int - i_g
    {
        if packets[i_usize] < packets[min_index_usize] {
            min_index_usize = i_usize;
            proof { min_index_g = min_index_usize as int; }
        }
        i_usize += 1;
        proof { i_g = i_usize as int; }
    }
    let mut res: Vec<i8> = Vec::new();
    res.push(1_i8);
    let second: i8 = (min_index_usize + 1) as i8;
    res.push(second);
    proof {
        assert(res@.len() == 2);
        assert((res@)[0] == 1);
        assert((res@)[1] == (min_index_usize as int) + 1);
        assert(1 <= (res@)[1] && (res@)[1] <= n_int);
        assert(forall|j: int| 0 <= j < seq.len() ==> seq[min_index_g] <= seq[j]);
        assert(forall|k: int| 0 <= k < min_index_g ==> seq[k] > seq[min_index_g]);
    }
    res
}

// </vc-code>


}

fn main() {}