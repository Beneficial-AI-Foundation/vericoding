// Author: Shaobo He

// ATOM 
// Author: Shaobo He

predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}


// ATOM 

lemma uniqueSqrt(x: int, r1: int, r2: int)
requires x >= 0 && r1 >= 0 && r2 >= 0;
ensures sqrt(x, r1) && sqrt(x, r2) ==> r1 == r2
{}


// SPEC 

method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
{
}


