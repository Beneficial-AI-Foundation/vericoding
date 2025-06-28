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
    
    // The proof is straightforward since students > 0 implies students - 1 < students
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // Definition of result
    assert(result < students);  // This follows directly from arithmetic
    
    result
}

}