use vstd::prelude::*;

verus! {

//IMPL unique
/* code modified by LLM (iteration 4): Fixed loop invariant to properly establish insertion position properties */
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..a.len()
        invariant
            forall|x: int, y: int|
                #![trigger result[x], result[y]]
                0 <= x && x < y && y < result.len() ==> result[x] < result[y],
    {
        let val = a[i];
        let mut should_add = true;
        
        for j in 0..result.len()
            invariant
                forall|x: int, y: int|
                    #![trigger result[x], result[y]]
                    0 <= x && x < y && y < result.len() ==> result[x] < result[y],
                should_add ==> forall|k: int| 0 <= k && k < j ==> result[k] != val,
        {
            if result[j] == val {
                should_add = false;
                break;
            }
        }
        
        if should_add {
            let mut insert_pos = result.len();
            
            /* code modified by LLM (iteration 4): Strengthened loop invariant to properly track insertion position */
            for j in 0..result.len()
                invariant
                    forall|x: int, y: int|
                        #![trigger result[x], result[y]]
                        0 <= x && x < y && y < result.len() ==> result[x] < result[y],
                    0 <= insert_pos && insert_pos <= result.len(),
                    forall|k: int| 0 <= k && k < j ==> (result[k] >= val ==> insert_pos <= k),
                    forall|k: int| 0 <= k && k < j && result[k] < val ==> k < insert_pos as int,
                    insert_pos < result.len() ==> result[insert_pos as int] >= val,
                    insert_pos == result.len() || result[insert_pos as int] > val,
            {
                if result[j] > val {
                    insert_pos = j;
                    break;
                }
            }
            
            /* code modified by LLM (iteration 4): Added helper assertions to establish properties before insertion */
            // Establish that all elements before insert_pos are < val
            assert(forall|k: int| 0 <= k && k < insert_pos as int ==> {
                let old_result_k = result[k];
                old_result_k < val
            });
            
            // Establish that all elements from insert_pos onwards are > val
            assert(forall|k: int| insert_pos as int <= k && k < result.len() ==> result[k] > val);
            
            result.insert(insert_pos, val);
            
            /* code modified by LLM (iteration 4): Strengthened post-insertion assertions */
            // After insertion, prove the sorted property is maintained
            assert(forall|x: int, y: int| {
                &&& 0 <= x < y < result.len()
                &&& x < insert_pos as int && y == insert_pos as int
            } ==> result[x] < result[y]);
            
            assert(forall|x: int, y: int| {
                &&& 0 <= x < y < result.len()
                &&& x == insert_pos as int && y > insert_pos as int
            } ==> result[x] < result[y]);
            
            assert(forall|x: int, y: int| {
                &&& 0 <= x < y < result.len()
                &&& x < insert_pos as int && y > insert_pos as int
            } ==> result[x] < result[y]);
        }
    }
    
    result
}

fn main() {}
}