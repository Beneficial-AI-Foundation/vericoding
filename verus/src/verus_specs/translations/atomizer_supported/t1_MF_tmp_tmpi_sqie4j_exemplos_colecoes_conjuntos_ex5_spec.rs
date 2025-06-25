// ATOM 
spec fn to_seq<T>(a: &[T], i: int) -> (res: Seq<T>)
    requires 0 <= i <= a.len()
    ensures res == a.subrange(i as int, a.len() as int)
{
    if i == a.len() {
        seq![]
    } else {
        seq![a[i as usize]].add(to_seq(a, i + 1))
    }
}

// SPEC 

pub fn Main()
{
}