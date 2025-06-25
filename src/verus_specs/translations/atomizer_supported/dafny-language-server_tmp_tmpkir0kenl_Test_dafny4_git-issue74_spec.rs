spec fn f(x: int) -> int {
    x
}

proof fn L()
    ensures forall|x: int| f(x) == x
{
}