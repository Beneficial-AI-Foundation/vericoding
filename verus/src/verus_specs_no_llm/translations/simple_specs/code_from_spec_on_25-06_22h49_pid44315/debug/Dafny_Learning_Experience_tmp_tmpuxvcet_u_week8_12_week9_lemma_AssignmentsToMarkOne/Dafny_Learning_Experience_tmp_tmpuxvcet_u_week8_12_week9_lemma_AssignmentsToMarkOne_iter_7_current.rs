use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AssignmentsToMarkOne(students: int, tutors: int) -> (r: int)
    requires
        students > 0 && tutors > 1
    ensures
        r < students
{
    let result = students - 1;
    
    // Proof annotations to help Verus verify the postcondition
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // By definition
    
    // Explicit arithmetic reasoning: if students > 0, then students >= 1
    assert(students >= 1);
    // Therefore students - 1 < students
    assert(students - 1 < students) by {
        // Verus should be able to prove this with basic arithmetic
        assert(students - 1 + 1 == students);
        assert(students - 1 + 1 > students - 1);
    }
    
    result
}

}