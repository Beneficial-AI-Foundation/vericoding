//ATOM

predicate relationOnASet<T>(R: set<(T,T)>, S: set<T>) {
  forall ts :: ts in R ==> ts.0 in S && ts.1 in S
}


//ATOM

predicate reflexive<T>(R: set<(T,T)>, S: set<T>) 
  requires relationOnASet(R, S)
{
  forall s :: s in S ==> (s,s) in R
}


//ATOM


function eight(x: nat):nat {
  9 * x + 5
}


//ATOM

function nineteenf(x: nat): nat {
  7*x+4
}


//ATOM

predicate equivalenceRelation<T>(R: set<(T,T)>, S: set<T>) 
  requires relationOnASet(R, S)
{
  reflexive(R, S) && symmetric(R, S) && transitive(R, S)
}


//ATOM

predicate transitive<T>(R: set<(T,T)>, S: set<T>) 
  requires relationOnASet(R, S)
{
  forall a,b,c :: a in S && b in S && c in S && (a,b) in R && (b,c) in R ==> (a,c) in R
}


//ATOM

predicate symmetric<T>(R: set<(T,T)>, S: set<T>)
  requires relationOnASet(R, S)
{
  forall x: T, y:T :: x in S && y in S && (x,y) in R ==> (y, x) in R
}


//ATOM

predicate isEven(x: nat) {
  x % 2 == 0
}


// SPEC

method test() {
}
