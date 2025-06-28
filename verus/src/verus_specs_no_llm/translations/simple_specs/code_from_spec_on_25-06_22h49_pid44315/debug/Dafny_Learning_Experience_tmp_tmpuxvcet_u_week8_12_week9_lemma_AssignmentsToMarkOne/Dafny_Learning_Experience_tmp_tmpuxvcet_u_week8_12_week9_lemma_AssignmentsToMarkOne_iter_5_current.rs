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
    
    // Simple arithmetic reasoning: students - 1 < students
    assert(students - 1 < students) by {
        // This is a basic arithmetic fact: x - 1 < x for any x
        assert(students == (students - 1) + 1);
        // Since students = (students - 1) + 1, we have students - 1 + 1 = students
        // Therefore students - 1 < students - 1 + 1 = students
    };
    
    result
}

}