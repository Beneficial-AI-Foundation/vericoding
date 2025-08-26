lemma DivisionLemma(n:int,d:int) 
    requires n > 0 && d>1
    ensures n/d < n
{
    // The proof follows from the fact that for integers, if n > 0 and d > 1,
    // then n/d (integer division) is strictly less than n
    assert d > 1;
    assert n > 0;
    // For integer division, n/d * d + (n % d) == n
    // Since d > 1, we have n/d <= n/d * d < n
    
    // More rigorous proof:
    // By the division algorithm: n == (n/d) * d + (n % d) where 0 <= (n % d) < d
    // Since d > 1, if n/d >= n, then (n/d) * d >= n * d > n
    // But (n/d) * d + (n % d) == n, so (n/d) * d <= n
    // This gives us n < (n/d) * d <= n, which is a contradiction
    // Therefore n/d < n
    
    if n/d >= n {
        assert (n/d) * d >= n * d;
        assert n * d >= n * 1;
        assert n * 1 == n;
        assert d > 1;
        assert n * d > n;
        assert (n/d) * d > n;
        // But we know n == (n/d) * d + (n % d) and (n % d) >= 0
        // So (n/d) * d <= n, which contradicts (n/d) * d > n
        assert (n/d) * d + (n % d) == n;
        assert (n % d) >= 0;
        assert (n/d) * d <= n;
        assert false; // contradiction
    }
}
// </vc-helpers>

// <vc-spec>
method AssignmentsToMark(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
// </vc-spec>
// <vc-code>
{
  r := students / tutors;
  DivisionLemma(students, tutors);
}
// </vc-code>


method AssignmentsToMarkOne(students:int, tutors: int) returns (r:int)
    requires students > 0 && tutors > 1
    ensures r < students
{

    r:= students/tutors;

    calc == {
        true;
        1/tutors < 1;
        students/tutors < students;
    }
}

lemma CommonElement(a:array<nat>, b:array<nat>)
    requires a.Length> 0 && b.Length > 0 && a[0] == b[0]
    ensures multiset(a[..])  * multiset(b[..]) == multiset([a[0]]) + multiset(a[1..]) * multiset(b[1..])
    //ensures multiset{a[..]}  * multiset{b[..]} == multiset([a[0]]) + multiset{a[1..]} * multiset{b[1..]}
{
    // Adding a body to remove the warning about bodyless method
    var E := multiset([a[0]]);
    assert a[..] == [a[0]] + a[1..];
    assert b[..] == [b[0]] + b[1..];
    assert a[0] == b[0];
    assert multiset(a[..]) == E + multiset(a[1..]);
    assert multiset(b[..]) == E + multiset(b[1..]);
}
/*
{
    var E := multiset{a[0]};
    calc =={
        multiset(a[..]) * multiset(b[..]);
        assert (a[..] == [a[0]] + a[1..]) && (b[..] == [b[0]] + b[1..]); 
        (E+ multiset(a[1..])) * (E + multiset(a[1..]));
        E + multiset(a[1..]) * multiset(b[1..]);
    }
}*/