// SPEC 
method Triple(x: int) returns (r: int)
{
}


// SPEC 

method TripleIf(x: int) returns (r: int) {
}


// SPEC 

method TripleOver(x: int) returns (r: int) {
}


// SPEC 

method TripleConditions(x: int) returns (r: int) 
requires x % 2 == 0
ensures r == 3 * x
{
}


// SPEC 

method Caller() {
}




