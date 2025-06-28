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
    assert(students > 0);  // From precondition
    assert(result == students - 1);  // Definition of result
    assert(1 > 0);  // Explicit fact about 1
    assert(students - 1 < students);  // Now provable: students - 1 = students + (-1) < students + 0 = students
    result
}

}