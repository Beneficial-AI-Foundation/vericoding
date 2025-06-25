pub fn update_map<K, V>(m1: Map<K, V>, m2: Map<K, V>) -> (r: Map<K, V>)
    ensures(forall|k: K| m2.contains_key(k) ==> r.contains_key(k))
    ensures(forall|k: K| m1.contains_key(k) ==> r.contains_key(k))
    ensures(forall|k: K| m2.contains_key(k) ==> r[k] == m2[k])
    ensures(forall|k: K| !m2.contains_key(k) && m1.contains_key(k) ==> r[k] == m1[k])
    ensures(forall|k: K| !m2.contains_key(k) && !m1.contains_key(k) ==> !r.contains_key(k))
{
}