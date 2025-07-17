// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AssignmentsToMark(students: int, tutors: int) -> r:int
    requires
        students > 0 && tutors > 1
    ensures
        r < students
;

proof fn lemma_AssignmentsToMark(students: int, tutors: int) -> (r: int)
    requires
        students > 0 && tutors > 1
    ensures
        r < students
{
    0
}

}