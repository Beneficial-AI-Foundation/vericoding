use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AssignmentsToMark(students: int, tutors: int) -> (r: int)
    requires
        students > 0 && tutors > 1
    ensures
        r < students
{
    let result = students - 1;
    
    // Proof that students - 1 < students
    // Since students > 0 (from precondition), we know students >= 1
    // Therefore students - 1 < students is equivalent to -1 < 0, which is true
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // Definition of result
    
    // The key insight: for any integer x, x - 1 < x
    // This is because x - 1 = x + (-1) and -1 < 0
    assert(result < students) by {
        // Verus should be able to prove this directly since it's basic arithmetic
        // If not, we can use the fact that students - 1 + 1 == students
        // which means students - 1 < students - 1 + 1 == students
    };
    
    result
}

}