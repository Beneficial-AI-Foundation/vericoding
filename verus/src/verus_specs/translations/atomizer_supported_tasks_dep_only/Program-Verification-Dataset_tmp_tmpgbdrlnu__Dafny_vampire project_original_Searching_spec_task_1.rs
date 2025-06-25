pub fn Find(blood: &[i32], key: i32) -> (index: i32)
    requires(true)
    ensures(|index: i32| 0 <= index ==> index < blood.len() && blood[index as usize] == key)
    ensures(|index: i32| index < 0 ==> forall|k: usize| 0 <= k < blood.len() ==> blood[k] != key)
{
}