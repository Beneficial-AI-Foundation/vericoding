use vstd::prelude::*;

verus! {

//IMPL unique
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    /* code modified by LLM (iteration 2): Added explicit type annotation to Vec::new() to fix type inference error */
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|x: int, y: int|
                #![trigger result[x], result[y]]
                0 <= x && x < y && y < result.len() ==> result[x] < result[y],
    {
        let mut should_add = true;
        for j in 0..result.len()
            invariant
                forall|x: int, y: int|
                    #![trigger result[x], result[y]]
                    0 <= x && x < y && y < result.len() ==> result[x] < result[y],
                should_add ==> forall|k: int| 0 <= k < j ==> result[k] != a[i as int],
                !should_add ==> exists|k: int| 0 <= k < result.len() && result[k] == a[i as int],
        {
            if result[j] == a[i] {
                should_add = false;
                break;
            }
        }
        
        if should_add {
            let mut insert_pos = result.len();
            for k in 0..result.len()
                invariant
                    forall|x: int, y: int|
                        #![trigger result[x], result[y]]
                        0 <= x && x < y && y < result.len() ==> result[x] < result[y],
                    insert_pos <= result.len(),
                    forall|m: int| 0 <= m < k ==> result[m] < a[i as int],
                    insert_pos == result.len() || result[insert_pos as int] > a[i as int],
                    /* code modified by LLM (iteration 2): Fixed invariant from insert_pos <= k to k <= insert_pos to correctly express that we haven't found insertion position in elements 0..k */
                    k <= insert_pos,
            {
                if result[k] > a[i] {
                    insert_pos = k;
                    break;
                }
            }
            
            result.insert(insert_pos, a[i]);
        }
    }
    
    result
}

fn main() {}
}