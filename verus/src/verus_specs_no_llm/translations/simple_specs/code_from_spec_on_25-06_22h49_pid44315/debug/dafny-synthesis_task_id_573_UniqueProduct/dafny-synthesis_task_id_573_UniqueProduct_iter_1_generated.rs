use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SetProduct(s: Set<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        1
    } else {
        let x = s.choose();
        x * SetProduct(s.remove(x))
    }
}

fn UniqueProduct(arr: Vec<int>) -> (product: int)
    ensures
        product == SetProduct((set i | 0 <= i < arr.len() :: arr.spec_index(i)))
{
    let mut unique_elements: Vec<int> = Vec::new();
    let mut i = 0;
    
    // Collect unique elements
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < unique_elements.len() ==> 
                exists|k: int| 0 <= k < i && arr.spec_index(k) == unique_elements.spec_index(j),
            forall|j1: int, j2: int| 0 <= j1 < j2 < unique_elements.len() ==> 
                unique_elements.spec_index(j1) != unique_elements.spec_index(j2),
    {
        let element = arr[i];
        let mut found = false;
        let mut j = 0;
        
        // Check if element is already in unique_elements
        while j < unique_elements.len()
            invariant
                0 <= j <= unique_elements.len(),
                found <==> exists|k: int| 0 <= k < j && unique_elements.spec_index(k) == element,
        {
            if unique_elements[j] == element {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            unique_elements.push(element);
        }
        i += 1;
    }
    
    // Calculate product of unique elements
    let mut product = 1;
    let mut k = 0;
    
    while k < unique_elements.len()
        invariant
            0 <= k <= unique_elements.len(),
            product == SetProduct((set j | 0 <= j < k :: unique_elements.spec_index(j))),
            forall|j1: int, j2: int| 0 <= j1 < j2 < unique_elements.len() ==> 
                unique_elements.spec_index(j1) != unique_elements.spec_index(j2),
            (set j | 0 <= j < unique_elements.len() :: unique_elements.spec_index(j)) == 
                (set i | 0 <= i < arr.len() :: arr.spec_index(i)),
    {
        product = product * unique_elements[k];
        k += 1;
    }
    
    product
}

}

The implementation works as follows:


   - First collects unique elements from the input array by iterating through and checking for duplicates
   - Then calculates the product of these unique elements
   - Uses loop invariants to maintain the relationship between the collected unique elements and the original array's unique elements
   - The final invariant ensures that the set of unique elements we collected matches the set comprehension in the postcondition

The key insight is that the postcondition requires the product to equal `SetProduct` applied to the set of all unique elements in the array (expressed as a set comprehension). The implementation maintains this relationship through carefully crafted loop invariants that establish the correspondence between the algorithmic approach and the specification.