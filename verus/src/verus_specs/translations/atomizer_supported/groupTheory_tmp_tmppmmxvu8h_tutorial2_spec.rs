// ATOM 
pub fn M1()
{
    assume(1 == 2);
}

// ATOM 
pub fn IntersectionIsSubsetOfBoth(A: set<int>, B: set<int>, C: set<int>)
    requires(C == A & B)
    ensures(C <= A && C <= B)
{}

// ATOM 
pub fn BothSetsAreSubsetsOfTheirUnion(A: set<int>, B: set<int>, C: set<int>)
    requires(C == A | B)
    ensures(A <= C && B <= C)
{}

const s0: set<int> = set![3, 8, 1];

// ATOM 
pub fn M2()
{
}

// ATOM 
pub fn TheEmptySetIsASubsetOfAnySet(A: set<int>, B: set<int>)
    requires(A == set![])
    ensures(A <= B)
{}

// ATOM 
pub fn AnySetIsASubsetOfItself(A: set<int>)
    ensures(A <= A)
{}

// ATOM 
pub fn TheIntersectionOfTwoSetsIsASubsetOfTheirUnion(A: set<int>, B: set<int>, C: set<int>, D: set<int>)
    requires(C == A & B && D == A | B)
    ensures(C <= D)
{}