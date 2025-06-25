spec fn f(x: int) -> int;

proof fn f_positive(x: int)
    requires x >= 0
    ensures f(x) >= 0
{
}

proof fn f_2_pos()
    ensures f(2) >= 0
{
}

proof fn f_1_1_pos()
    ensures f(1 + 1) >= 0
{
}