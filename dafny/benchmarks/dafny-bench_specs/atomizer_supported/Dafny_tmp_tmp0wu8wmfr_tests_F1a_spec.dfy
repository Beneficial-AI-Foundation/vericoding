// SPEC 
method F() returns ( r: int)
    ensures r <= 0
{
}


// SPEC 

method Main() 
{
}



// SPEC 


method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;

{
}


