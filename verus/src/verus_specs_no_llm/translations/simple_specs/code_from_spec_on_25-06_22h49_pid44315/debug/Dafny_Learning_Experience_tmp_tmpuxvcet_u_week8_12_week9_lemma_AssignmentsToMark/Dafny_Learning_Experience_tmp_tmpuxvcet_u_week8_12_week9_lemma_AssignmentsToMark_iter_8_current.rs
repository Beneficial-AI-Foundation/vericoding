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
    // Therefore students - 1 < students
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // Definition of result
    
    // For any integer x, x - 1 < x is a basic arithmetic fact
    assert(result < students);
    
    result
}

}