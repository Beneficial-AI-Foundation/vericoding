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

// Helper spec function to compute product of a sequence
spec fn seq_product(v: Seq<int>) -> int
    decreases v.len()
{
    if v.len() == 0 {
        1
    } else {
        v[0] * seq_product(v.subrange(1, v.len() as int))
    }
}

// Lemma to relate seq_product to SetProduct when sequence has unique elements
proof fn seq_product_eq_set_product(v: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]
    ensures
        seq_product(v) == SetProduct(v.to_set())
    decreases v.len()
{
    if v.len() == 0 {
        assert(v.to_set() == Set::empty());
    } else {
        let rest = v.subrange(1, v.len() as int);
        assert(forall|i: int, j: int| 0 <= i < j < rest.len() ==> rest[i] != rest[j]);
        seq_product_eq_set_product(rest);
        
        let s = v.to_set();
        let x = v[0];
        assert(s.contains(x));
        assert(rest.to_set() == s.remove(x));
    }
}

// Helper lemma for seq_product with push
proof fn seq_product_push(v: Seq<int>, x: int)
    ensures seq_product(v.push(x)) == seq_product(v) * x
    decreases v.len()
{
    if v.len() == 0 {
        assert(v.push(x) == seq![x]);
        assert(seq_product(v.push(x)) == x);
        assert(seq_product(v) == 1);
    } else {
        let v_tail = v.subrange(1, v.len() as int);
        seq_product_push(v_tail, x);
        assert(v.push(x).subrange(1, v.push(x).len() as int) == v_tail.push(x));
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
            // All elements in unique_elements come from arr[0..i]
            forall|j: int| 0 <= j < unique_elements.len() ==> 
                exists|k: int| 0 <= k < i && arr.spec_index(k) == unique_elements.spec_index(j),
            // unique_elements has no duplicates
            forall|j1: int, j2: int| 0 <= j1 < j2 < unique_elements.len() ==> 
                unique_elements.spec_index(j1) != unique_elements.spec_index(j2),
            // Every unique element from arr[0..i] is in unique_elements
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < unique_elements.len() && 
                unique_elements.spec_index(j) == arr.spec_index(k),
            // Set equivalence
            (set j | 0 <= j < unique_elements.len() :: unique_elements.spec_index(j)) == 
                (set k | 0 <= k < i :: arr.spec_index(k)),
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
            // Product so far equals seq_product of elements processed
            product == seq_product(unique_elements@.subrange(0, k as int)),
            // unique_elements has no duplicates
            forall|j1: int, j2: int| 0 <= j1 < j2 < unique_elements.len() ==> 
                unique_elements.spec_index(j1) != unique_elements.spec_index(j2),
            // unique_elements represents the same set as the specification
            (set j | 0 <= j < unique_elements.len() :: unique_elements.spec_index(j)) == 
                (set i | 0 <= i < arr.len() :: arr.spec_index(i)),
    {
        product = product * unique_elements[k];
        
        // Prove the relationship with seq_product
        let subrange_k = unique_elements@.subrange(0, k as int);
        let subrange_k_plus_1 = unique_elements@.subrange(0, (k+1) as int);
        
        assert(subrange_k_plus_1 == subrange_k.push(unique_elements[k]));
        seq_product_push(subrange_k, unique_elements[k]);
        
        k += 1;
    }
    
    // Prove final postcondition
    assert(unique_elements@.subrange(0, unique_elements.len() as int) == unique_elements@);
    seq_product_eq_set_product(unique_elements@);
    
    product
}

}