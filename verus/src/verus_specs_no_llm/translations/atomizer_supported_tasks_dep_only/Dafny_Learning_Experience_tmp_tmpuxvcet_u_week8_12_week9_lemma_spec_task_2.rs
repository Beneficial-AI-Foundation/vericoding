// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AssignmentsToMarkOne(students: int, tutors: int) -> r:int
    requires
        students > 0 && tutors > 1
    ensures
        r < students
;

proof fn lemma_AssignmentsToMarkOne(students: int, tutors: int) -> (r: int)
    requires
        students > 0 && tutors > 1
    ensures
        r < students
{
    0
}

}