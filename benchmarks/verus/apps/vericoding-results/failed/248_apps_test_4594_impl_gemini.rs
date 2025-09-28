// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(diameters: Seq<int>) -> bool {
    diameters.len() > 0 && forall|i: int| 0 <= i < diameters.len() ==> diameters[i] > 0
}

spec fn num_distinct(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.subrange(1, s.len() as int).contains(s[0]) {
        num_distinct(s.subrange(1, s.len() as int))
    } else {
        1 + num_distinct(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn seq_is_distinct(s: Seq<int>) -> bool {
    s.len() == s.to_set().len()
}

/* helper modified by LLM (iteration 4): expanded proof for set properties */
proof fn lemma_num_distinct_is_set_len(s: Seq<int>)
    ensures num_distinct(s) == s.to_set().len()
    decreases s.len()
{
    if s.len() > 0 {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_num_distinct_is_set_len(s_tail);
        
        assert(s.to_set() =~~= s_tail.to_set().insert(s[0]));
        
        if s_tail.contains(s[0]) {
            assert(s_tail.to_set().contains(s[0]));
            assert(s_tail.to_set().insert(s[0]) =~~= s_tail.to_set());
        } else {
            assert(!s_tail.to_set().contains(s[0]));
            assert(s_tail.to_set().insert(s[0]).len() == s_tail.to_set().len() + 1);
        }
    }
}

/* helper modified by LLM (iteration 4): fixed variable shadowing in map */
fn vec_contains(v: &Vec<i8>, val: i8) -> (result: bool)
    ensures result <==> v@.map(|_idx, x| x as int).contains(val as int)
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            !v@.subrange(0, i as int).map(|_idx, x| x as int).contains(val as int)
        decreases v.len() - i
    {
        if v[i] == val {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn solve(diameters: Vec<i8>) -> (result: i8)
    requires 
        valid_input(diameters@.map(|i, x| x as int)),
    ensures 
        result as int == num_distinct(diameters@.map(|i, x| x as int)),
        result as int >= 1,
        result as int <= diameters@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed variable shadowing and added proof blocks */
    let mut uniques: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let ghost s_int = diameters@.map(|_idx, x| x as int);
    assert(s_int.len() == diameters.len());

    while i < diameters.len()
        invariant
            0 <= i <= diameters.len(),
            seq_is_distinct(uniques@.map(|_idx, x| x as int)),
            uniques@.map(|_idx, x| x as int).to_set()
                =~~= s_int.subrange(0, i as int).to_set(),
            uniques@.len() <= 127,
        decreases diameters.len() - i
    {
        let d = diameters[i];
        let is_present = vec_contains(&uniques, d);
        
        proof {
            let ghost uniques_int_old = uniques@.map(|_idx, x| x as int);
            let ghost prefix_int_old = s_int.subrange(0, i as int);
            if is_present {
                assert(uniques_int_old.contains(d as int));
                assert(uniques_int_old.to_set().contains(d as int));
                assert(prefix_int_old.to_set().contains(d as int));
            }
        }

        if !is_present {
            uniques.push(d);
        }
        i = i + 1;
    }

    proof {
        lemma_num_distinct_is_set_len(s_int);
    }
    
    return uniques.len() as i8;
}
// </vc-code>


}

fn main() {}