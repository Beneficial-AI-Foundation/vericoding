// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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
    return 0;
}

}