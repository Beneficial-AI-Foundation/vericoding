use vstd::prelude::*;

verus! {

spec fn rotate_right_precond(l: Seq<i32>, n: nat) -> bool {
    true
}

spec fn rotate_right_postcond(l: Seq<i32>, n: nat, result: Seq<i32>) -> bool {
    &&& result.len() == l.len()
    &&& (forall |i: int| 0 <= i < l.len() ==> {
        let len = l.len();
        let rotated_index = ((i - (n as int) + (len as int)) % (len as int));
        #[trigger] result[i] == l[rotated_index]
    })
}

fn rotate_right(l: Vec<i32>, n: usize) -> (result: Vec<i32>)
    requires rotate_right_precond(l@, n as nat)
    ensures rotate_right_postcond(l@, n as nat, result@)
{
    if l.len() == 0 {
        return Vec::new();
    }
    
    let len = l.len();
    let mut result = Vec::with_capacity(len);
    let effective_n = n % len; // Reduce n modulo len to handle cases where n >= len
    
    for i in 0..len
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < i ==> {
                let rotated_index = ((j - (n as int) + (len as int)) % (len as int));
                #[trigger] result@[j] == l@[rotated_index]
            }
    {
        /* code modified by LLM (iteration 1): replaced int arithmetic with usize arithmetic for executable code */
        let rotated_index = if i >= effective_n {
            i - effective_n
        } else {
            len - effective_n + i
        };
        result.push(l[rotated_index]);
        
        /* code modified by LLM (iteration 1): added proof block to establish correspondence between usize and int calculations */
        proof {
            let ghost_rotated_index = ((i as int - n as int + len as int) % len as int);
            // The usize calculation is equivalent to the ghost int calculation
            assert(rotated_index as int == ghost_rotated_index);
        }
    }
    
    result
}

}

fn main() {}