pub fn min_pair(s: Seq<int>) -> (r: int)
    requires
        s.len() == 2,
    ensures
        s[0] <= s[1] <==> r == s[0],
        s[0] > s[1] ==> r == s[1],
{
}

pub fn min(s: Seq<int>) -> (r: int)
    requires
        s.len() >= 2,
    ensures
        forall|i: int| 0 <= i < s.len() ==> r <= s[i],
{
}

pub fn second_smallest(s: &[int]) -> (second_smallest: int)
    requires
        s.len() >= 2,
        exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i as int] == min(s@) && s[j as int] != s[i as int],
    ensures
        exists|i: usize, j: usize| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i as int] == min(s@) && s[j as int] == second_smallest,
        forall|k: usize| 0 <= k < s.len() && s[k as int] != min(s@) ==> s[k as int] >= second_smallest,
{
}