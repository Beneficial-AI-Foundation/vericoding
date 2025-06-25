pub fn maxSeq(v: Vec<i32>) -> (max: i32)
    requires(v.len() >= 1)
    ensures(|max: i32| forall|i: usize| 0 <= i < v.len() ==> max >= v[i])
    ensures(|max: i32| exists|i: usize| 0 <= i < v.len() && max == v[i])
{
}