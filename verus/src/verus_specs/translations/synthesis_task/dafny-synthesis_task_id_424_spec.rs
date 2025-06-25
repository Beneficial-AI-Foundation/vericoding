pub fn extract_rear_chars(l: Seq<Seq<char>>) -> (r: Seq<char>)
    requires(
        forall|i: int| 0 <= i < l.len() ==> l[i].len() > 0
    )
    ensures(|r: Seq<char>|
        r.len() == l.len() &&
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i][l[i].len() - 1]
    )
{
}