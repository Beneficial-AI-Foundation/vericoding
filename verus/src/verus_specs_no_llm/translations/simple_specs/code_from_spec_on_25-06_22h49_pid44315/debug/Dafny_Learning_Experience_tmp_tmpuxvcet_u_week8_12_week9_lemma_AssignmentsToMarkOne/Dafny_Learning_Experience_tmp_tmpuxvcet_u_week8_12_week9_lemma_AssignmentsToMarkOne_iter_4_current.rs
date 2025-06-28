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
    
    // More explicit arithmetic reasoning
    assert(students >= 1);  // Since students > 0 and students is int
    assert(students - 1 < students) by {
        // This arithmetic fact should be provable directly
        assert(students == (students - 1) + 1);
        assert((students - 1) + 1 > students - 1);
    };
    
    result
}

}