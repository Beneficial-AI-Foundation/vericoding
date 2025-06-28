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
        assert(SetProduct(Set::empty()) == 1);
        assert(seq_product(v) == 1);
    } else {
        let rest = v.subrange(1, v.len() as int);
        assert(forall|i: int, j: int| 0 <= i < j < rest.len() ==> rest[i] != rest[j]) by {
            assert(forall|i: int, j: int| 0 <= i < j < rest.len() ==> {
                &&& rest[i] == v[i+1]
                &&& rest[j] == v[j+1]
                &&& 1 <= i+1 < j+1 < v.len()
                &&& v[i+1] != v[j+1]
            });
        };
        seq_product_eq_set_product(rest);
        
        let s = v.to_set();
        let x = v[0];
        assert(s.contains(x));
        
        // Prove that rest.to_set() == s.remove(x)
        assert(rest.to_set() =~= s.remove(x)) by {
            assert(forall|y: int| rest.to_set().contains(y) <==> s.remove(x).contains(y)) by {
                assert(forall|y: int| #[trigger] rest.to_set().contains(y) ==> {
                    &&& (exists|i: int| 0 <= i < rest.len() && rest[i] == y)
                    &&& (exists|i: int| 1 <= i < v.len() && v[i] == y)
                    &&& s.contains(y)
                    &&& y != x  // because v[0] = x and all elements are unique
                });
                assert(forall|y: int| #[trigger] s.remove(x).contains(y) ==> {
                    &&& s.contains(y) 
                    &&& y != x
                    &&& (exists|i: int| 0 <= i < v.len() && v[i] == y)
                    &&& (exists|i: int| 1 <= i < v.len() && v[i] == y)  // can't be at index 0 since v[0] = x
                    &&& rest.to_set().contains(y)
                });
            };
        };
        
        // Now we can use the recursive call result
        assert(seq_product(rest) == SetProduct(rest.to_set()));
        assert(seq_product(rest) == SetProduct(s.remove(x)));
        assert(seq_product(v) == x * seq_product(rest));
        assert(SetProduct(s) == x * SetProduct(s.remove(x)));
        assert(seq_product(v) == SetProduct(s));
    }
}

// Helper lemma for seq_product with push
proof fn seq_product_push(v: Seq<int>, x: int)
    ensures seq_product(v.push(x)) == seq_product(v) * x
    decreases v.len()
{
    if v.len() == 0 {
        assert(v.push(x) =~= seq![x]);
        assert(seq_product(seq![x]) == x);
        assert(seq_product(v) == 1);
    } else {
        let v_tail = v.subrange(1, v.len() as int);
        let pushed = v.push(x);
        assert(pushed.len() == v.len() + 1);
        assert(pushed[0] == v[0]);
        assert(pushed.subrange(1, pushed.len() as int) =~= v_tail.push(x)) by {
            let pushed_tail = pushed.subrange(1, pushed.len() as int);
            let v_tail_pushed = v_tail.push(x);
            assert(pushed_tail.len() == v_tail_pushed.len());
            assert(forall|i: int| 0 <= i < pushed_tail.len() ==> pushed_tail[i] == v_tail_pushed[i]);
        };
        seq_product_push(v_tail, x);
        assert(seq_product(pushed.subrange(1, pushed.len() as int)) == seq_product(v_tail) * x);
        assert(seq_product(pushed) == pushed[0] * seq_product(pushed.subrange(1, pushed.len() as int)));
        assert(seq_product(pushed) == v[0] * (seq_product(v_tail) * x));
        assert(seq_product(v) == v[0] * seq_product(v_tail));
        assert(seq_product(pushed) == seq_product(v) * x);
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
        
        assert(subrange_k_plus_1 =~= subrange_k.push(unique_elements[k])) by {
            assert(subrange_k_plus_1.len() == subrange_k.len() + 1);
            assert(forall|idx: int| 0 <= idx < subrange_k.len() ==> 
                subrange_k_plus_1[idx] == subrange_k[idx]);
            assert(subrange_k_plus_1[subrange_k.len()] == unique_elements[k]);
        };
        
        seq_product_push(subrange_k, unique_elements[k]);
        
        k += 1;
    }
    
    // Prove final postcondition
    assert(unique_elements@.subrange(0, unique_elements.len() as int) =~= unique_elements@);
    
    // Apply the lemma to show seq_product equals SetProduct
    seq_product_eq_set_product(unique_elements@);
    
    assert(unique_elements@.to_set() =~= 
        (set j | 0 <= j < unique_elements.len() :: unique_elements.spec_index(j)));
    
    product
}

}