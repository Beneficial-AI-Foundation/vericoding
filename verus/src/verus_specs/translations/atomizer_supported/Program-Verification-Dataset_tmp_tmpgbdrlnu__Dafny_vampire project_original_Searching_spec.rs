pub fn Find(blood: &[int], key: int) -> (index: int)
    requires(true)
    ensures(|index: int| 0 <= index ==> index < blood.len() && blood[index] == key)
    ensures(|index: int| index < 0 ==> forall|k: int| 0 <= k < blood.len() ==> blood[k] != key)
{
}