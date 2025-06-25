pub fn string_swap(s: Seq<char>, i: nat, j: nat) -> (t: Seq<char>)
    requires(
        i >= 0 && j >= 0 && s.len() >= 0
    )
    requires(
        s.len() > 0 ==> i < s.len() && j < s.len()
    )
    ensures(|t|
        s.to_multiset() == t.to_multiset()
    )
    ensures(|t|
        s.len() == t.len()
    )
    ensures(|t|
        s.len() > 0 ==> forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int]
    )
    ensures(|t|
        s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int]
    )
    ensures(|t|
        s.len() == 0 ==> t == s
    )
{
}