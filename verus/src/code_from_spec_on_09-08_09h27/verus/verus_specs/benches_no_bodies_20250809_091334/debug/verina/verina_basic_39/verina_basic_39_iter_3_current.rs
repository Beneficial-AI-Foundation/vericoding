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
    
    let mut result = Vec::with_capacity(l.len());
    let len = l.len();
    let effective_n = n % len;
    
    let mut i = 0;
    while i < len
        invariant
            len == l.len(),
            effective_n == n % len,
            result.len() == i,
            len > 0,
            i <= len,
            forall |j: int| 0 <= j < i ==> {
                let rotated_index = ((j - (effective_n as int) + (len as int)) % (len as int));
                #[trigger] result@[j] == l@[rotated_index]
            }
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases len - i
    {
        let source_index = if i >= effective_n {
            i - effective_n
        } else {
            i + len - effective_n
        };
        
        result.push(l[source_index]);
        
        proof {
            let rotated_index = ((i as int - effective_n as int + len as int) % len as int);
            assert(rotated_index >= 0);
            assert(rotated_index < len as int);
            if i >= effective_n {
                assert(rotated_index == (i - effective_n) as int);
            } else {
                assert(rotated_index == (i + len - effective_n) as int);
            }
        }
        
        i += 1;
    }
    
    proof {
        /* code modified by LLM (iteration 2): added explicit triggers to resolve verification error */
        assert(forall |j: int| 0 <= j < l.len() ==> {
            let rotated_index = ((j - (n as int) + (l.len() as int)) % (l.len() as int));
            #[trigger] rotated_index == ((j - (effective_n as int) + (l.len() as int)) % (l.len() as int))
        }) by {
            assert(forall |j: int| 0 <= j < l.len() ==> {
                let a = (j - (n as int) + (l.len() as int)) % (l.len() as int);
                let b = (j - (effective_n as int) + (l.len() as int)) % (l.len() as int);
                #[trigger] a == b
            });
        }
    }
    
    result
}

}

fn main() {}