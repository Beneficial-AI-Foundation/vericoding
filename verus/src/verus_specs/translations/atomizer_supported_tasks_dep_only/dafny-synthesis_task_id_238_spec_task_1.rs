pub fn count_non_empty_substrings(s: &str) -> (count: i32)
    ensures(count >= 0),
    ensures(count == (s.len() * (s.len() + 1)) / 2),
{
}