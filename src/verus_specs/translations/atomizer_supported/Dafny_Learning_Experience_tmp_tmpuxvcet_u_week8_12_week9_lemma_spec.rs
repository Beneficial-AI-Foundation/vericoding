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

// SPEC 
pub fn AssignmentsToMarkOne(students: int, tutors: int) -> (r: int)
    requires(students > 0 && tutors > 1)
    ensures(|r: int| r < students)
{
}

// ATOM 
proof fn CommonElement(a: &[nat], b: &[nat])
    requires(a.len() > 0 && b.len() > 0 && a[0] == b[0])
    ensures(a@.to_multiset().intersect(b@.to_multiset()) == seq![a[0]].to_multiset().add(a@.subrange(1, a.len() as int).to_multiset().intersect(b@.subrange(1, b.len() as int).to_multiset())))
{
}