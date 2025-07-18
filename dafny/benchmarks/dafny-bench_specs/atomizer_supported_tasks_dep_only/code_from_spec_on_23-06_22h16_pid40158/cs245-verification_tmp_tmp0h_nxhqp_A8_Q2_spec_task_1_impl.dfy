// IMPL A8Q2 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

method A8Q1(x: int, y: int, z: int) returns (m: int)
/*Pre-Condition*/   requires true;
/*Post-Condition*/  ensures m<=x && m<=y && m<=z;
{
    if x <= y && x <= z {
        m := x;
    } else if y <= x && y <= z {
        m := y;
    } else {
        m := z;
    }
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/


/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/



/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/