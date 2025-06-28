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
    
    // The arithmetic fact that students - 1 < students when students > 0
    // This should be provable automatically by Verus arithmetic reasoning
    assert(students - 1 < students);
    
    result
}

}