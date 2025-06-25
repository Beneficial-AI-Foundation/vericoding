pub fn Foo(y: int, x: int) -> (z: int)
    requires(0 <= y)
    ensures(z == x*y)
{
}

pub fn stringToSet(s: Seq<char>) -> (r: Set<char>)
    ensures(forall|x: int| 0 <= x < s.len() ==> r.contains(s[x]))
{
}

pub fn Main()
{
}