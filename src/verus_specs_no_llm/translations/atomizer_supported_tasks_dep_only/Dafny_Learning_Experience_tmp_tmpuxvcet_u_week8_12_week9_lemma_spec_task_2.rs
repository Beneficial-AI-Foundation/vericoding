// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn AssignmentsToMarkOne(students: int, tutors: int) -> (r: int)
    requires students > 0 and tutors > 1
    ensures r < students
{
}

}