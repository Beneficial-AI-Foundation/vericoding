// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(lst: Seq<int>) -> bool {
    5 <= lst.len() <= 10 &&
    forall|i: int| 0 <= i < lst.len() ==> #[trigger] lst[i] >= 1 && #[trigger] lst[i] <= 32
}

spec fn int_xor(a: int, b: int) -> int {
    let a_bv = a as u32;
    let b_bv = b as u32;
    (a_bv ^ b_bv) as int
}

spec fn min_of_sequence(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let tail_min = min_of_sequence(s.skip(1));
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove min update correctness */
proof fn lemma_min_in_bounds(lst: Seq<int>)
    requires
        lst.len() > 0,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] >= 1 && lst[i] <= 32
    ensures
        1 <= min_of_sequence(lst) <= 32
    decreases lst.len()
{
    if lst.len() == 1 {
        assert(lst[0] >= 1 && lst[0] <= 32);
    } else {
        lemma_min_in_bounds(lst.skip(1));
        let tail_min = min_of_sequence(lst.skip(1));
        assert(lst[0] >= 1 && lst[0] <= 32);
        if lst[0] <= tail_min {
            assert(min_of_sequence(lst) == lst[0]);
        } else {
            assert(min_of_sequence(lst) == tail_min);
        }
    }
}

proof fn lemma_min_update(lst: Seq<int>, idx: int)
    requires
        0 <= idx < lst.len(),
        lst.len() > 0
    ensures
        min_of_sequence(lst.take(idx + 1)) == if lst[idx] <= min_of_sequence(lst.take(idx)) { lst[idx] } else { min_of_sequence(lst.take(idx)) }
    decreases idx
{
    if idx == 0 {
        assert(lst.take(1) =~= seq![lst[0]]);
    } else {
        assert(lst.take(idx + 1) =~= lst.take(idx).push(lst[idx]));
        let prev_min = min_of_sequence(lst.take(idx));
        assert(min_of_sequence(lst.take(idx + 1)) == if lst[idx] <= prev_min { lst[idx] } else { prev_min });
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(lst: Vec<i8>) -> (result: i8)
    requires valid_input(lst@.map(|i: int, x: i8| x as int))
    ensures result as int == 2 + int_xor(lst@[2] as int, min_of_sequence(lst@.map(|i: int, x: i8| x as int)))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed min computation and XOR calculation */
    let ghost lst_as_int = lst@.map(|i: int, x: i8| x as int);
    let mut min_val: i8 = lst[0];
    let mut idx: usize = 1;
    
    while idx < lst.len()
        invariant
            1 <= idx <= lst.len(),
            lst_as_int =~= lst@.map(|i: int, x: i8| x as int),
            min_val as int == min_of_sequence(lst_as_int.take(idx as int)),
            forall|i: int| 0 <= i < lst.len() ==> lst@[i] >= 1 && lst@[i] <= 32
        decreases lst.len() - idx
    {
        proof {
            lemma_min_update(lst_as_int, idx as int - 1);
            assert(lst_as_int.take(idx as int) =~= lst_as_int.take((idx - 1) as int).push(lst@[(idx - 1) as int] as int));
        }
        
        if lst[idx] < min_val {
            min_val = lst[idx];
        }
        
        proof {
            lemma_min_update(lst_as_int, idx as int);
            assert(lst_as_int.take((idx + 1) as int) =~= lst_as_int.take(idx as int).push(lst@[idx as int] as int));
            let curr_elem = lst@[idx as int] as int;
            let prev_min = min_of_sequence(lst_as_int.take(idx as int));
            if curr_elem <= prev_min {
                assert(min_val as int == curr_elem);
                assert(min_of_sequence(lst_as_int.take((idx + 1) as int)) == curr_elem);
            } else {
                assert(min_val as int == prev_min);
                assert(min_of_sequence(lst_as_int.take((idx + 1) as int)) == prev_min);
            }
        }
        
        idx = idx + 1;
    }
    
    assert(lst_as_int.take(lst.len() as int) =~= lst_as_int);
    proof {
        lemma_min_in_bounds(lst_as_int);
        assert(1 <= min_val && min_val <= 32);
        assert(1 <= lst@[2] && lst@[2] <= 32);
        assert((lst@[2] ^ min_val) <= 63);
    }
    
    let xor_val = (lst[2] as u8 ^ min_val as u8) as i8;
    assert(xor_val >= 0 && xor_val <= 63);
    assert(2 + xor_val <= 65);
    
    (2 + xor_val) as i8
}
// </vc-code>


}

fn main() {}