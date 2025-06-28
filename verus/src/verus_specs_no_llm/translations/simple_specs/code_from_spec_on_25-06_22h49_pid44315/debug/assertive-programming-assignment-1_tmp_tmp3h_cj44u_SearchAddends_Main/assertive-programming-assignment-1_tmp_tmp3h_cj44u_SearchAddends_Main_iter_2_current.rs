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
    assert(Sorted(empty_seq));
    true
}

// Helper function to check a simple sorted sequence
fn check_sorted_simple() -> (result: bool)
    ensures result == true
{
    let simple_seq: Seq<int> = seq![1, 2, 3];
    assert(Sorted(simple_seq)) by {
        assert forall|i: int, j: int| 0 <= i <= j < simple_seq.len() implies simple_seq.spec_index(i) <= simple_seq.spec_index(j) by {
            if 0 <= i <= j < simple_seq.len() {
                if i == 0 && j == 0 {
                    assert(simple_seq.spec_index(0) == 1);
                    assert(simple_seq.spec_index(0) <= simple_seq.spec_index(0));
                } else if i == 0 && j == 1 {
                    assert(simple_seq.spec_index(0) == 1);
                    assert(simple_seq.spec_index(1) == 2);
                    assert(1 <= 2);
                } else if i == 0 && j == 2 {
                    assert(simple_seq.spec_index(0) == 1);
                    assert(simple_seq.spec_index(2) == 3);
                    assert(1 <= 3);
                } else if i == 1 && j == 1 {
                    assert(simple_seq.spec_index(1) == 2);
                    assert(simple_seq.spec_index(1) <= simple_seq.spec_index(1));
                } else if i == 1 && j == 2 {
                    assert(simple_seq.spec_index(1) == 2);
                    assert(simple_seq.spec_index(2) == 3);
                    assert(2 <= 3);
                } else if i == 2 && j == 2 {
                    assert(simple_seq.spec_index(2) == 3);
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
    assert(HasAddends(test_seq, 4)) by {
        assert(0 <= 0 < 1 < test_seq.len());
        assert(test_seq.spec_index(0) + test_seq.spec_index(1) == 1 + 3);
        assert(1 + 3 == 4);
    }
    true
}

}