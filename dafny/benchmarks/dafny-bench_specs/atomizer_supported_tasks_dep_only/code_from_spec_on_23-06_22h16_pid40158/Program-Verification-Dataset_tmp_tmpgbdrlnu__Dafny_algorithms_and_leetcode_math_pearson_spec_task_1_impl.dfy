// ATOM 
function eight(x: nat):nat {
    9 * x + 5
}

//IMPL isOdd
predicate isOdd(x: nat) {
    x % 2 == 1
}

// ATOM 
predicate isEven(x: nat) {
    x % 2 == 0
}

// ATOM 
function nineteenf(x: nat): nat {
    7*x+4
}

//IMPL nineteens
function nineteens(x: nat): nat {
    19 * x
}

//IMPL nineteenlemma
lemma nineteenlemma(x: nat)
    ensures nineteens(x) == 19 * x
{
    /* code modified by LLM (iteration 1): Added trivial proof body since nineteens(x) directly returns 19 * x */
}

//IMPL relationDomain
function relationDomain<T>(R: set<(T,T)>): set<T> {
    /* code modified by LLM (iteration 1): Fixed set comprehension syntax by adding proper range expression */
    set x | x in (set p | p in R :: p.0)
}

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

//IMPL notTrueAlways
predicate notTrueAlways() {
    false
}

//IMPL test
method test() {
}