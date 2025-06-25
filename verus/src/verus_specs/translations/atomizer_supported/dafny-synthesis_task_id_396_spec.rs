pub fn start_and_end_with_same_char(s: &str) -> (result: bool)
    requires
        s.len() > 0,
    ensures
        result <==> s@[0] == s@[s@.len() - 1],
{
}