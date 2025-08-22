

// ATOM 


function eight(x: nat):nat {
    9 * x + 5
}


//ATOM_PLACEHOLDER_isOdd

// ATOM 

predicate isEven(x: nat) {
    x % 2 == 0
}


// ATOM 


function eight(x: nat):nat {
    9 * x + 5
}
L

// ATOM 

function nineteenf(x: nat): nat {
    7*x+4
}

//ATOM_PLACEHOLDER_nineteens

//ATOM_PLACEHOLDER_nineteenlemma

//ATOM_PLACEHOLDER_relationDomain

// ATOM 

predicate reflexive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall s :: s in S ==> (s,s) in R
}


// ATOM 

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
    requires relationOnASet(R, S)
{
    forall x: T, y:T :: x in S && y in S && (x,y) in R ==> (y, x) in R
}


// ATOM 

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}


// ATOM 

predicate equivalenceRelation<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    reflexive(R, S) && symmetric(R, S) && transitive(R, S)
}


// ATOM 

predicate relationOnASet<T>(R: set<(T,T)>, S: set<T>) {
    forall ts :: ts in R ==> ts.0 in S && ts.1 in S
}


// lemma equivUnion<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires equivalenceRelation(R_1, S_1)
//     requires equivalenceRelation(R_2, S_2)
//     ensures equivalenceRelation(R_1+R_2, S_1+S_2)
// {
//     reflexiveUnion(R_1, S_1, R_2, S_2);
//     symmetricUnion(R_1, S_1, R_2, S_2);
//     transitiveUnion(R_1, S_1, R_2, S_2);
// }

// ATOM 

predicate reflexive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall s :: s in S ==> (s,s) in R
}
Union

// ATOM 

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
    requires relationOnASet(R, S)
{
    forall x: T, y:T :: x in S && y in S && (x,y) in R ==> (y, x) in R
}
Union

    
// ATOM 

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}
Union

// lemma transitiveUnionContra<T>(R_1: set<(T,T)>, S_1: set<T>, R_2: set<(T,T)>, S_2: set<T>)
//     requires |R_1| > 0
//     requires |R_2| > 0
//     requires |S_1| > 0
//     requires |S_2| > 0
//     requires relationOnASet(R_1, S_1)
//     requires relationOnASet(R_2, S_2)
//     requires transitive(R_1, S_1)
//     requires transitive(R_2, S_2)
//     ensures exists (R_1+R_2, S_1+S_2) :: !transitive(R_1+R_2, S_1+S_2) 
// {
//     assume S_1 * S_2 != {};
//     if transitive(R_1 + R_2, S_1+S_2) {
//         forall a,b,c | a in S_1+S_2 && b in S_1+S_2 && c in S_1+S_2 && (a,b) in R_1+R_2 && (b,c) in R_1+R_2 
//             ensures (a,c) in R_1+R_2 
//         {
//             if a in S_1 && a !in S_2 && b in S_1 && b in S_2 && c in S_2 && c !in S_1 {
//                 assert (a,c) !in R_1;
//                 assert (a,c) !in R_2;
//                 assert (a,c) !in R_1+R_2;
//                 assert false;
//             }
//         } 
//     }
// }

// ATOM 

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
    requires relationOnASet(R, S)
{
    forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}
UnionContra

//ATOM_PLACEHOLDER_notTrueAlways

// SPEC 

method test() {
}


