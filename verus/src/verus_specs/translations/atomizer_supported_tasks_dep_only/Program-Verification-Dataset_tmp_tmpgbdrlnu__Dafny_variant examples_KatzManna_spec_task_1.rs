pub fn NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> z: int
    ensures(proveFunctionalPostcondition ==> z == if x > 101 { x-10 } else { 91 })
{
}