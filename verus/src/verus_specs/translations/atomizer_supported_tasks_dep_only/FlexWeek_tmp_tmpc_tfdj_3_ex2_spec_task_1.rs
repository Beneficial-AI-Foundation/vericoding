fn abs(a: int) -> nat {
    if a < 0 { -a } else { a }
}

pub fn aba(a: &[int]) -> Vec<int>
    ensures |result| == a.len(),
    ensures forall|x: usize| 0 <= x < result.len() ==> result[x] == abs(a[x]),
{
}