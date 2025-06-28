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
        // Base case is trivial
    } else {
        let rest = v.subrange(1, v.len() as int);
        
        // Prove rest also has unique elements
        assert(forall|i: int, j: int| 0 <= i < j < rest.len() ==> rest[i] != rest[j]) by {
            assert(forall|i: int, j: int| 0 <= i < j < rest.len() ==> {
                let vi = i + 1;
                let vj = j + 1;
                rest[i] == v[vi] && rest[j] == v[vj] && 0 <= vi < vj < v.len()
            });
        };
        
        // Recursive call
        seq_product_eq_set_product(rest);
        
        let s = v.to_set();
        let x = v[0];
        
        // Prove that rest.to_set() == s.remove(x)
        assert(rest.to_set() == s.remove(x)) by {
            assert(forall|y: int| rest.to_set().contains(y) <==> s.remove(x).contains(y)) by {
                assert(forall|y: int| rest.to_set().contains(y) ==> {
                    exists|i: int| 1 <= i < v.len() && v[i] == y
                });
                
                assert(forall|y: int| rest.to_set().contains(y) ==> y != x) by {
                    assert(forall|y: int| rest.to_set().contains(y) ==> {
                        exists|i: int| 1 <= i < v.len() && v[i] == y && v[i] != v[0]
                    });
                };
                
                assert(forall|y: int| s.remove(x).contains(y) ==> rest.to_set().contains(y)) by {
                    assert(forall|y: int| s.contains(y) && y != x ==> {
                        exists|i: int| 0 <= i < v.len() && v[i] == y && i != 0
                    });
                };
            };
        };
    }
}

// Helper lemma for seq_product with push
proof fn seq_product_push(v: Seq<int>, x: int)
    ensures seq_product(v.push(x)) == seq_product(v) * x
    decreases v.len()
{
    if v.len() == 0 {
        // Base case
    } else {
        let v_tail = v.subrange(1, v.len() as int);
        let pushed = v.push(x);
        
        // Show that pushed.subrange(1, pushed.len()) == v_tail.push(x)
        assert(pushed.subrange(1, pushed.len() as int) == v_tail.push(x)) by {
            let pushed_tail = pushed.subrange(1, pushed.len() as int);
            let v_tail_pushed = v_tail.push(x);
            assert(pushed_tail.len() == v_tail_pushed.len());
            assert(forall|i: int| 0 <= i < pushed_tail.len() ==> pushed_tail[i] == v_tail_pushed[i]);
        };
        
        // Recursive call
        seq_product_push(v_tail, x);
    }
}

fn UniqueProduct(arr: Vec<int>) -> (product: int)
    ensures
        product == SetProduct((set i | 0 <= i < arr.len() :: arr@[i]))
{
    let mut unique_elements: Vec<int> = Vec::new();
    let mut i = 0;
    
    // Collect unique elements
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            // All elements in unique_elements come from arr[0..i]
            forall|j: int| 0 <= j < unique_elements.len() ==> 
                exists|k: int| 0 <= k < i && arr@[k] == unique_elements@[j],
            // unique_elements has no duplicates
            forall|j1: int, j2: int| 0 <= j1 < j2 < unique_elements.len() ==> 
                unique_elements@[j1] != unique_elements@[j2],
            // Every unique element from arr[0..i] is in unique_elements
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < unique_elements.len() && 
                unique_elements@[j] == arr@[k],
            // Set equivalence
            (set j | 0 <= j < unique_elements.len() :: unique_elements@[j]) == 
                (set k | 0 <= k < i :: arr@[k]),
    {
        let element = arr[i];
        let mut found = false;
        let mut j = 0;
        
        // Check if element is already in unique_elements
        while j < unique_elements.len()
            invariant
                0 <= j <= unique_elements.len(),
                found <==> exists|k: int| 0 <= k < j && unique_elements@[k] == element,
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
                unique_elements@[j1] != unique_elements@[j2],
            // unique_elements represents the same set as the specification
            (set j | 0 <= j < unique_elements.len() :: unique_elements@[j]) == 
                (set i | 0 <= i < arr.len() :: arr@[i]),
    {
        let old_product = product;
        let subrange_k = unique_elements@.subrange(0, k as int);
        
        product = product * unique_elements[k];
        
        // Prove the relationship with seq_product
        let subrange_k_plus_1 = unique_elements@.subrange(0, (k+1) as int);
        
        assert(subrange_k_plus_1 == subrange_k.push(unique_elements@[k as int])) by {
            assert(subrange_k_plus_1.len() == subrange_k.len() + 1);
            assert(forall|idx: int| 0 <= idx < subrange_k.len() ==> 
                subrange_k_plus_1[idx] == subrange_k[idx]);
            assert(subrange_k_plus_1[subrange_k.len()] == unique_elements@[k as int]);
        };
        
        seq_product_push(subrange_k, unique_elements@[k as int]);
        
        k += 1;
    }
    
    // Prove final postcondition
    assert(unique_elements@.subrange(0, unique_elements.len() as int) == unique_elements@);
    assert(product == seq_product(unique_elements@));
    
    // Apply the lemma to show seq_product equals SetProduct
    seq_product_eq_set_product(unique_elements@);
    assert(seq_product(unique_elements@) == SetProduct(unique_elements@.to_set()));
    
    // Show set equivalence
    assert(unique_elements@.to_set() == 
        (set j | 0 <= j < unique_elements.len() :: unique_elements@[j])) by {
        assert(forall|x: int| unique_elements@.to_set().contains(x) <==> 
            (set j | 0 <= j < unique_elements.len() :: unique_elements@[j]).contains(x));
    };
    
    product
}

}