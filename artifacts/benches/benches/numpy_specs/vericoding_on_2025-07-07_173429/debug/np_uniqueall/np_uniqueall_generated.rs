use vstd::prelude::*;

verus! {

fn unique_all(arr: &Vec<i32>) -> (ret: Vec<i32>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> exists|j: int| 0 <= j < ret.len() && ret[j] == #[trigger] arr[i],
        forall|i: int, j: int| 0 <= i < ret.len() && 0 <= j < i ==> #[trigger] ret[i] != #[trigger] ret[j],
{
    let mut result: Vec<i32> = Vec::new();
    let mut count = 0;
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= count <= i <= arr.len(),
            result.len() == count,
            forall|k: int| 0 <= k < count ==> exists|m: int| 0 <= m < i && #[trigger] result[k] == #[trigger] arr[m],
            forall|k: int| 0 <= k < i ==> exists|m: int| 0 <= m < count && #[trigger] result[m] == #[trigger] arr[k],
            forall|k: int, m: int| 0 <= k < count && 0 <= m < k ==> #[trigger] result[k] != #[trigger] result[m],
        decreases arr.len() - i,
    {
        let mut found = false;
        let mut j = 0;
        
        while j < count
            invariant
                j <= count,
                count == result.len(),
                i < arr.len(),
                forall|k: int| 0 <= k < j ==> #[trigger] result[k] != arr[i as int],
            decreases count - j,
        {
            if result[j] == arr[i] {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(arr[i]);
            count = count + 1;
        }
        
        i += 1;
    }
    
    result
}

fn main() {}

}