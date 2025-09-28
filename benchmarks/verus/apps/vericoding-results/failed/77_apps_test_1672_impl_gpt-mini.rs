// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(magnets: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < magnets.len() ==> 
        (magnets[i].len() == 2 && 
         ((magnets[i][0] == '0' && magnets[i][1] == '1') || 
          (magnets[i][0] == '1' && magnets[i][1] == '0')))
}

spec fn count_groups(magnets: Seq<Seq<char>>) -> int {
    if magnets.len() == 0 { 
        0 as int
    } else { 
        1 + (Set::new(|i: int| 1 <= i < magnets.len() && magnets[i] != magnets[i-1]).len() as int)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Vec equality iff Seq equality */
proof fn vec_eq_iff(a: Vec<char>, b: Vec<char>)
    ensures
        a == b <==> a@ == b@,
{
    proof {
        assert(a == b <==> a@ == b@);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(magnets: Vec<Vec<char>>) -> (result: usize)
    requires 
        valid_input(magnets@.map(|i, v: Vec<char>| v@))
    ensures 
        result >= 0,
        magnets@.len() == 0 ==> result == 0,
        magnets@.len() > 0 ==> result >= 1,
        result <= magnets@.len(),
        valid_input(magnets@.map(|i, v: Vec<char>| v@)) ==> result == count_groups(magnets@.map(|i, v: Vec<char>| v@)) as usize
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): count groups using usize loop, update tracked ghosts inside proof blocks, and prove equality to spec */
    let n_usize: usize = magnets.len();
    if n_usize == 0 {
        return 0;
    }
    let mut count_usize: usize = 1;
    let mut i_usize: usize = 1;
    let tracked n: int = n_usize as int;
    let tracked mut count: int = 1 as int;
    let tracked mut i: int = 1 as int;
    while i_usize < n_usize
        invariant
            0 as int <= i && i <= n,
            count == if i == 0 as int { 0 as int } else { 1 as int + (Set::new(|k: int| 1 as int <= k && k < i && (magnets@)@[k] != (magnets@)@[k-1]).len() as int) },
        decreases n - i
    {
        if magnets[i_usize] != magnets[i_usize - 1] {
            count_usize += 1;
            proof { count = count + 1 as int; }
        }
        i_usize += 1;
        proof { i = i + 1 as int; }
    }
    let result: usize = count_usize;
    proof {
        if valid_input(magnets@.map(|i, v: Vec<char>| v@)) {
            if magnets@.len() == 0 {
                assert(result == 0);
            } else {
                assert(count == 1 as int + (Set::new(|k: int| 1 as int <= k && k < n && (magnets@)@[k] != (magnets@)@[k-1]).len() as int));
                assert(count == count_groups(magnets@.map(|j, v: Vec<char>| v@)));
                assert(result == count as usize);
            }
        }
    }
    result
}

// </vc-code>


}

fn main() {}