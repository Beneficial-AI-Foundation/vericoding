pub fn index_wise_addition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires(a.len() > 0 && b.len() > 0)
    requires(a.len() == b.len())
    requires(forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len())
    ensures(result.len() == a.len())
    ensures(forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len())
    ensures(forall|i: int| 0 <= i < result.len() ==> forall|j: int| 0 <= j < result[i].len() ==> result[i][j] == a[i][j] + b[i][j])
{
}