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
    // Since students > 0, we can prove students - 1 < students
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // Definition of result
    
    // Use arithmetic reasoning: if students > 0, then students >= 1
    // Therefore students - 1 < students
    assert(students >= 1) by {
        // students > 0 implies students >= 1 for integers
    };
    
    assert(students - 1 < students) by {
        // Basic arithmetic: for any integer x >= 1, x - 1 < x
        assert(students >= 1);
    };
    
    assert(result < students);
    
    result
}

}