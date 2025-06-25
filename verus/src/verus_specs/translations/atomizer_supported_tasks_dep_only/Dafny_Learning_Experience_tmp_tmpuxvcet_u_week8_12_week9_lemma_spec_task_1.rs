// SPEC 
pub fn AssignmentsToMark(students: int, tutors: int) -> (r: int)
    requires(students > 0 && tutors > 1)
    ensures(|r: int| r < students)
{
}

// ATOM 
proof fn DivisionLemma(n: int, d: int)
    requires(n > 0 && d > 1)
    ensures(n / d < n)
{
}