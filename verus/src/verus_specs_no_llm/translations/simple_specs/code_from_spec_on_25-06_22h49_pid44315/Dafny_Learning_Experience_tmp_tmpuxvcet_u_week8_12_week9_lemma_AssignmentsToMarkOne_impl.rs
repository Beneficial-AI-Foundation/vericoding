use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn assignments_to_mark_one(students: int, tutors: int) -> (r: int)
    requires
        students > 0 && tutors > 1
    ensures
        r < students
{
    let result = students - 1;
    
    // Proof annotations to help Verus verify the postcondition
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // By definition
    
    // The arithmetic fact that students - 1 < students when students > 0
    assert(students - 1 < students) by {
        // Since students > 0, we know students >= 1
        // Therefore students - 1 >= 0
        // And students = (students - 1) + 1
        // So students > students - 1
        assert(students >= 1);
        assert(students == (students - 1) + 1);
    };
    
    result
}

}