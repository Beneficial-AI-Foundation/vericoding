//ATOM_PLACEHOLDER_F

//ATOM_PLACEHOLDER_Main

//IMPL Mid
method Mid( p: int, q: int) returns ( m: int )
    // | ... | ??? | ... |
    //        p m   q
    requires p <= q;
    ensures p<= m <= q;
    ensures m-p <= q-m;
    ensures 0 <= (q-m)-(m-p) <= 1;
{
    m := (p + q) / 2;
}