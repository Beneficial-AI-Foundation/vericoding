pub fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    requires(
        true
    )
    ensures(|s: Vec<i32>| 
        s.len() == a.len() &&
        forall|i: usize| 0 <= i < a.len() ==> s[i] == a[i]
    )
{
    
}