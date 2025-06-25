pub fn get_first_elements(lst: Seq<Seq<int>>) -> (result: Seq<int>)
    requires
        forall|i: int| 0 <= i < lst.len() ==> lst[i].len() > 0,
    ensures
        |result: Seq<int>| result.len() == lst.len(),
        |result: Seq<int>| forall|i: int| 0 <= i < result.len() ==> result[i] == lst[i][0],
{
}