use vstd::prelude::*;

verus! {

// ATOM 

spec fn eight(x: nat) -> nat {
    9 * x + 5
}

// ATOM 

spec fn isOdd(x: nat) -> bool {
    x % 2 == 1
}

// ATOM 

spec fn isEven(x: nat) -> bool {
    x % 2 == 0
}

// ATOM 

proof fn eightL(x: nat)
    requires(isOdd(x))
    ensures(isEven(eight(x)))
{

}

// ATOM 

spec fn nineteenf(x: nat) -> nat {
    7*x+4
}

// ATOM 
spec fn nineteens(x: nat) -> nat {
    3*x+11
}

// ATOM 

proof fn nineteenlemma(x: nat) 
    requires(isEven(nineteenf(x)))
    ensures(isOdd(nineteens(x)))
{

}

// ATOM 

spec fn relationDomain<T>(s: Set<(T,T)>) -> Set<T> {
    set_choose(|z: (T,T)| s.contains(z), |z: (T,T)| z.0)
}

// ATOM 

spec fn reflexive<T>(R: Set<(T,T)>, S: Set<T>) -> bool
    recommends(relationOnASet(R, S))
{
    forall|s: T| S.contains(s) ==> R.contains((s,s))
}

// ATOM 

spec fn symmetric<T>(R: Set<(T,T)>, S: Set<T>) -> bool
    recommends(relationOnASet(R, S))
{
    forall|x: T, y: T| S.contains(x) && S.contains(y) && R.contains((x,y)) ==> R.contains((y, x))
}

// ATOM 

spec fn transitive<T>(R: Set<(T,T)>, S: Set<T>) -> bool
    recommends(relationOnASet(R, S))
{
    forall|a: T, b: T, c: T| S.contains(a) && S.contains(b) && S.contains(c) && R.contains((a,b)) && R.contains((b,c)) ==> R.contains((a,c))
}

// ATOM 

spec fn equivalenceRelation<T>(R: Set<(T,T)>, S: Set<T>) -> bool
    recommends(relationOnASet(R, S))
{
    reflexive(R, S) && symmetric(R, S) && transitive(R, S)
}

// ATOM 

spec fn relationOnASet<T>(R: Set<(T,T)>, S: Set<T>) -> bool {
    forall|ts: (T,T)| R.contains(ts) ==> S.contains(ts.0) && S.contains(ts.1)
}

// ATOM 

proof fn reflexiveUnion<T>(R_1: Set<(T,T)>, S_1: Set<T>, R_2: Set<(T,T)>, S_2: Set<T>)
    requires(R_1.len() > 0)
    requires(R_2.len() > 0)
    requires(S_1.len() > 0)
    requires(S_2.len() > 0)
    requires(relationOnASet(R_1, S_1))
    requires(relationOnASet(R_2, S_2))
    requires(reflexive(R_1, S_1))
    requires(reflexive(R_2, S_2))
    ensures(reflexive(R_1.union(R_2), S_1.union(S_2)))
{

}

// ATOM 

proof fn symmetricUnion<T>(R_1: Set<(T,T)>, S_1: Set<T>, R_2: Set<(T,T)>, S_2: Set<T>)
    requires(R_1.len() > 0)
    requires(R_2.len() > 0)
    requires(S_1.len() > 0)
    requires(S_2.len() > 0)
    requires(relationOnASet(R_1, S_1))
    requires(relationOnASet(R_2, S_2))
    requires(symmetric(R_1, S_1))
    requires(symmetric(R_2, S_2))
    ensures(symmetric(R_1.union(R_2), S_1.union(S_2)))
{

}

// ATOM 

proof fn transitiveUnion<T>(R_1: Set<(T,T)>, S_1: Set<T>, R_2: Set<(T,T)>, S_2: Set<T>)
    requires(R_1.len() > 0)
    requires(R_2.len() > 0)
    requires(S_1.len() > 0)
    requires(S_2.len() > 0)
    requires(relationOnASet(R_1, S_1))
    requires(relationOnASet(R_2, S_2))
    requires(transitive(R_1, S_1))
    requires(transitive(R_2, S_2))
    ensures(transitive(R_1.union(R_2), S_1.union(S_2)))
{

}

// ATOM 

proof fn transitiveUnionContra<T>() -> (R1: Set<(T, T)>, S1: Set<T>, R2: Set<(T, T)>, S2: Set<T>)
    ensures(relationOnASet(R1, S1))
    ensures(relationOnASet(R2, S2))
    ensures(transitive(R1, S1))
    ensures(transitive(R2, S2))
    ensures(!transitive(R1.union(R2), S1.union(S2)))
{

}

// ATOM 

proof fn notTrueAlways<T>()
    ensures(!(forall|S1: Set<T>, S2: Set<T>, R1: Set<(T,T)>, R2: Set<(T, T)>| 
        relationOnASet(R1, S1) &&
        relationOnASet(R2, S2) &&
        transitive(R1, S1) &&
        transitive(R2, S2) ==> transitive(R1.union(R2), S1.union(S2))))
{

}

// SPEC 

pub fn test() {

}

}