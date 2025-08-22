use vstd::prelude::*;

verus! {

// Predicate to check if a sequence is sorted (pairwise ordering)
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

// Precondition: both input lists are sorted
spec fn merge_sorted_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    is_sorted(a) && is_sorted(b)
}

// Postcondition: result is sorted and is a permutation of concatenated inputs
spec fn merge_sorted_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    is_sorted(result) && result =~= a + b
}

// Auxiliary recursive merge function - structure matches original Lean code
fn merge_sorted_aux(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires
        is_sorted(a@) && is_sorted(b@),
    ensures
        is_sorted(result@) && result@ =~= a@ + b@,
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        return b;
    }
    if b.len() == 0 {
        return a;
    }
    
    let a_head = a[0];
    let b_head = b[0];
    
    if a_head <= b_head {
        let mut a_tail = Vec::new();
        for i in 1..a.len() {
            a_tail.push(a[i]);
        }
        let merged_tail = merge_sorted_aux(a_tail, b);
        let mut result = Vec::new();
        result.push(a_head);
        for i in 0..merged_tail.len() {
            result.push(merged_tail[i]);
        }
        
        proof {
            assert(a@ == seq![a_head] + a_tail@);
            assert(result@ == seq![a_head] + merged_tail@);
            assert(merged_tail@ =~= a_tail@ + b@);
            assert(result@ =~= seq![a_head] + a_tail@ + b@);
            assert(result@ =~= a@ + b@);
            
            // Prove sortedness
            assert forall|i: int, j: int| 0 <= i < j < result.len() implies result@[i] <= result@[j] by {
                if i == 0 {
                    if j < merged_tail.len() + 1 {
                        assert(result@[j] == merged_tail@[j-1]);
                        if j-1 < a_tail.len() {
                            assert(merged_tail@[j-1] == a_tail@[j-1]);
                            assert(a_tail@[j-1] == a@[j]);
                            assert(a_head <= a@[j]);
                        } else {
                            assert(a_head <= b_head);
                        }
                    }
                } else {
                    assert(result@[i] == merged_tail@[i-1]);
                    assert(result@[j] == merged_tail@[j-1]);
                    assert(merged_tail@[i-1] <= merged_tail@[j-1]);
                }
            };
        }
        
        result
    } else {
        let mut b_tail = Vec::new();
        for i in 1..b.len() {
            b_tail.push(b[i]);
        }
        let merged_tail = merge_sorted_aux(a, b_tail);
        let mut result = Vec::new();
        result.push(b_head);
        for i in 0..merged_tail.len() {
            result.push(merged_tail[i]);
        }
        
        proof {
            assert(b@ == seq![b_head] + b_tail@);
            assert(result@ == seq![b_head] + merged_tail@);
            assert(merged_tail@ =~= a@ + b_tail@);
            assert(result@ =~= seq![b_head] + a@ + b_tail@);
            assert(result@ =~= a@ + b@);
            
            // Prove sortedness
            assert forall|i: int, j: int| 0 <= i < j < result.len() implies result@[i] <= result@[j] by {
                if i == 0 {
                    if j < merged_tail.len() + 1 {
                        assert(result@[j] == merged_tail@[j-1]);
                        if j-1 < a.len() {
                            assert(merged_tail@[j-1] == a@[j-1]);
                            assert(b_head < a_head);
                            assert(a_head <= a@[j-1]);
                            assert(b_head <= a@[j-1]);
                        } else {
                            assert(b_head <= b@[j-1-a.len()+1]);
                        }
                    }
                } else {
                    assert(result@[i] == merged_tail@[i-1]);
                    assert(result@[j] == merged_tail@[j-1]);
                    assert(merged_tail@[i-1] <= merged_tail@[j-1]);
                }
            };
        }
        
        result
    }
}

// Main merge function
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires
        merge_sorted_precond(a@, b@),
    ensures
        merge_sorted_postcond(a@, b@, result@),
{
    merge_sorted_aux(a, b)
}

fn main() {}

} // verus!