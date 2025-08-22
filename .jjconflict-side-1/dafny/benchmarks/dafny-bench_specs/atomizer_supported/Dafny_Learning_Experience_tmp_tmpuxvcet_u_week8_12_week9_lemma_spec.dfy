// SPEC 
method AssignmentsToMark(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{
}


// ATOM 

lemma DivisionLemma(n:int,d:int) 
    requires n > 0 && d>1
    ensures n/d < n
// SPEC 


method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{
}


// ATOM 

lemma CommonElement(a:array<nat>, b:array<nat>)
    requires a.Length> 0 && b.Length > 0 && a[0] == b[0]
    ensures multiset(a[..])  * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
    //ensures multiset{a[..]}  * multiset{b[..]} == multiset([a[0]]) + multiset{a[1..]} * multiset{b[1..]}
/*
{
    var E := multiset{a[0]};
    calc =={
        multiset(a[..]) * multiset(b[..]);
        (E+ multiset(a[1..])) * (E + multiset(a[1..]));
        E + multiset(a[1..]) * multiset(b[1..]);
    }
}*/
  * multiset{b[..]} == multiset([a[0]]) + multiset{a[1..]} * multiset{b[1..]}
/*
{
    var E := multiset{a[0]};
    calc =={
        multiset(a[..]) * multiset(b[..]);
        (E+ multiset(a[1..])) * (E + multiset(a[1..]));
        E + multiset(a[1..]) * multiset(b[1..]);
    }
}*/
  * multiset{b[..]} == multiset([a[0]]) + multiset{a[1..]} * multiset{b[1..]}
/*
{
    var E := multiset{a[0]};
    calc =={
        multiset(a[..]) * multiset(b[..]);
        (E+ multiset(a[1..])) * (E + multiset(a[1..]));
        E + multiset(a[1..]) * multiset(b[1..]);
    }
}*/
