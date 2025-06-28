use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(q: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < q.len() ==> q.spec_index(i) <= q.spec_index(j)
}

spec fn HasAddends(q: Seq<int>, x: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < q.len() && q.spec_index(i) + q.spec_index(j) == x
}

// Helper function to demonstrate the specifications work
fn check_sorted_empty() -> (result: bool)
    ensures result == true
{
    let empty_seq: Seq<int> = seq![];
    assert(Sorted(empty_seq)) by {
        // For empty sequence, the universal quantifier is vacuously true
        assert forall|i: int, j: int| 0 <= i <= j < empty_seq.len() ==> empty_seq.spec_index(i) <= empty_seq.spec_index(j) by {
            // Since empty_seq.len() == 0, the condition 0 <= i <= j < 0 is never satisfied
            assert(empty_seq.len() == 0);
        }
    }
    true
}

// Helper function to check a simple sorted sequence
fn check_sorted_simple() -> (result: bool)
    ensures result == true
{
    let simple_seq: Seq<int> = seq![1, 2, 3];
    assert(simple_seq.len() == 3);
    assert(simple_seq.spec_index(0) == 1);
    assert(simple_seq.spec_index(1) == 2);
    assert(simple_seq.spec_index(2) == 3);
    
    assert(Sorted(simple_seq)) by {
        assert forall|i: int, j: int| 0 <= i <= j < simple_seq.len() ==> simple_seq.spec_index(i) <= simple_seq.spec_index(j) by {
            if 0 <= i <= j < simple_seq.len() {
                // We know simple_seq.len() == 3, so i, j are in {0, 1, 2}
                // Case analysis on all valid combinations of i and j
                assert(i == 0 || i == 1 || i == 2);
                assert(j >= i && (j == 0 || j == 1 || j == 2));
                
                // All cases where i <= j and both are valid indices
                if i == 0 && j == 0 {
                    assert(simple_seq.spec_index(0) <= simple_seq.spec_index(0));
                } else if i == 0 && j == 1 {
                    assert(1 <= 2);
                } else if i == 0 && j == 2 {
                    assert(1 <= 3);
                } else if i == 1 && j == 1 {
                    assert(simple_seq.spec_index(1) <= simple_seq.spec_index(1));
                } else if i == 1 && j == 2 {
                    assert(2 <= 3);
                } else if i == 2 && j == 2 {
                    assert(simple_seq.spec_index(2) <= simple_seq.spec_index(2));
                }
            }
        }
    }
    true
}

// Helper function to demonstrate HasAddends
fn check_has_addends() -> (result: bool)
    ensures result == true
{
    let test_seq: Seq<int> = seq![1, 3, 5];
    assert(test_seq.len() == 3);
    assert(test_seq.spec_index(0) == 1);
    assert(test_seq.spec_index(1) == 3);
    assert(test_seq.spec_index(2) == 5);
    
    assert(HasAddends(test_seq, 4)) by {
        // We need to show there exist i, j such that 0 <= i < j < test_seq.len() 
        // and test_seq.spec_index(i) + test_seq.spec_index(j) == 4
        // Let's use i = 0, j = 1
        assert(0 < 1);
        assert(1 < test_seq.len());
        assert(0 <= 0);
        assert(test_seq.spec_index(0) + test_seq.spec_index(1) == 1 + 3);
        assert(1 + 3 == 4);
        // This witnesses the existential quantifier
        assert(0 <= 0 < 1 < test_seq.len() && test_seq.spec_index(0) + test_seq.spec_index(1) == 4);
    }
    true
}

// Additional helper to test edge cases
fn check_sorted_two_elements() -> (result: bool)
    ensures result == true
{
    let two_seq: Seq<int> = seq![5, 10];
    assert(two_seq.len() == 2);
    assert(two_seq.spec_index(0) == 5);
    assert(two_seq.spec_index(1) == 10);
    
    assert(Sorted(two_seq)) by {
        assert forall|i: int, j: int| 0 <= i <= j < two_seq.len() ==> two_seq.spec_index(i) <= two_seq.spec_index(j) by {
            if 0 <= i <= j < two_seq.len() {
                // two_seq.len() == 2, so i, j are in {0, 1}
                assert(i == 0 || i == 1);
                assert(j >= i && (j == 0 || j == 1));
                
                if i == 0 && j == 0 {
                    assert(two_seq.spec_index(0) <= two_seq.spec_index(0));
                } else if i == 0 && j == 1 {
                    assert(5 <= 10);
                } else if i == 1 && j == 1 {
                    assert(two_seq.spec_index(1) <= two_seq.spec_index(1));
                }
            }
        }
    }
    true
}

// Additional test to verify HasAddends with different sum
fn check_has_addends_different_sum() -> (result: bool)
    ensures result == true
{
    let test_seq: Seq<int> = seq![1, 3, 5];
    assert(test_seq.len() == 3);
    assert(test_seq.spec_index(0) == 1);
    assert(test_seq.spec_index(1) == 3);
    assert(test_seq.spec_index(2) == 5);
    
    assert(HasAddends(test_seq, 8)) by {
        // Using i = 1, j = 2: test_seq[1] + test_seq[2] = 3 + 5 = 8
        assert(0 <= 1 < 2 < test_seq.len());
        assert(test_seq.spec_index(1) + test_seq.spec_index(2) == 3 + 5);
        assert(3 + 5 == 8);
        assert(1 < 2 < test_seq.len() && test_seq.spec_index(1) + test_seq.spec_index(2) == 8);
    }
    true
}

}