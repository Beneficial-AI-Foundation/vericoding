pub fn NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> z: int
    ensures(proveFunctionalPostcondition ==> z == if x > 101 { x-10 } else { 91 })
{
}

pub fn Gcd(x1: int, x2: int)
    requires(1 <= x1 && 1 <= x2)
{
}

pub fn Determinant(X: &mut [[int; M]; M], M: int) -> z: int
    requires(1 <= M)
{
}