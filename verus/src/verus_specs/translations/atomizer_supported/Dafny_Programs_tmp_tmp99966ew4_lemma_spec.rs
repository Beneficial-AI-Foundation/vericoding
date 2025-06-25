// ATOM 
proof fn SkippingLemma(a: &[int], j: int)
    requires a.len() >= 0
    requires forall|i: int| 0 <= i < a.len() ==> 0 <= a[i]
    requires forall|i: int| 0 < i < a.len() ==> a[i-1]-1 <= a[i]
    requires 0 <= j < a.len()
    ensures forall|k: int| j <= k < j + a[j] && k < a.len() ==> a[k] != 0
{
}

// SPEC 
pub fn FindZero(a: &[int]) -> (index: int)
    requires forall|i: int| 0 <= i < a.len() ==> 0 <= a[i]
    requires forall|i: int| 0 < i < a.len() ==> a[i-1]-1 <= a[i]
    ensures index < 0 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != 0
    ensures 0 <= index ==> index < a.len() && a[index] == 0
{
}