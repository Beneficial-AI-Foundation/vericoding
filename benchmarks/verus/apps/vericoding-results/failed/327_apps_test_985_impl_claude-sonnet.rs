// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(positions: Seq<(int, int)>) -> bool {
    positions.len() >= 1 && positions.len() <= 200000 &&
    (forall|i: int| 0 <= i < positions.len() ==> 
        1 <= #[trigger] positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall|i: int, j: int| 0 <= i < j < positions.len() ==> 
        #[trigger] positions[i] != #[trigger] positions[j])
}

spec fn count_attacking_pairs(positions: Seq<(int, int)>) -> int
    recommends valid_input(positions)
{
    /* Count pairs (i,j) where i < j and bishops at positions[i] and positions[j] attack each other */
    positions.len() * (positions.len() - 1) / 2 /* placeholder - actual implementation would count diagonal pairs */
}

spec fn valid_output(positions: Seq<(int, int)>, result: int) -> bool
    recommends valid_input(positions)
{
    result == count_attacking_pairs(positions) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow issues and strengthened preconditions */
fn abs_diff(a: i16, b: i16) -> (result: i16)
    requires
        -32767 <= a <= 32767,
        -32767 <= b <= 32767,
    ensures
        result >= 0,
        result == if a >= b { a - b } else { b - a },
{
    if a >= b {
        a - b
    } else {
        b - a
    }
}

spec fn bishops_attack(pos1: (int, int), pos2: (int, int)) -> bool {
    let (x1, y1) = pos1;
    let (x2, y2) = pos2;
    (if x1 >= x2 { x1 - x2 } else { x2 - x1 }) == (if y1 >= y2 { y1 - y2 } else { y2 - y1 })
}

spec fn count_attacking_pairs_correct(positions: Seq<(int, int)>) -> int
    recommends valid_input(positions)
{
    count_pairs_rec(positions, 0, 0)
}

spec fn count_pairs_rec(positions: Seq<(int, int)>, i: int, acc: int) -> int
    recommends
        valid_input(positions),
        0 <= i <= positions.len(),
        acc >= 0,
    decreases positions.len() - i
{
    if i >= positions.len() {
        acc
    } else {
        count_pairs_rec(positions, i + 1, acc + count_attacks_from(positions, i, i + 1))
    }
}

spec fn count_attacks_from(positions: Seq<(int, int)>, i: int, j: int) -> int
    recommends
        valid_input(positions),
        0 <= i < positions.len(),
        i <= j <= positions.len(),
    decreases positions.len() - j
{
    if j >= positions.len() {
        0
    } else {
        let attack_count: int = if bishops_attack(positions[i], positions[j]) { 1 } else { 0 };
        attack_count + count_attacks_from(positions, i, j + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_bishops(positions: Vec<(i8, i8)>) -> (result: u64)
    requires
        valid_input(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int))),
    ensures
        valid_output(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int)), result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow by using saturating addition and proper bounds */
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < positions.len()
        invariant
            i <= positions.len(),
            result <= u64::MAX,
        decreases positions.len() - i
    {
        let mut j: usize = i + 1;
        
        while j < positions.len()
            invariant
                i < positions.len(),
                i + 1 <= j <= positions.len(),
                result <= u64::MAX,
            decreases positions.len() - j
        {
            let pos1 = positions[i];
            let pos2 = positions[j];
            
            // Since positions are in range [1,1000], cast to i16 is safe
            let dx = abs_diff(pos1.0 as i16, pos2.0 as i16);
            let dy = abs_diff(pos1.1 as i16, pos2.1 as i16);
            
            if dx == dy {
                // Use saturating add to prevent overflow
                if result < u64::MAX {
                    result = result + 1;
                }
            }
            
            j = j + 1;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}