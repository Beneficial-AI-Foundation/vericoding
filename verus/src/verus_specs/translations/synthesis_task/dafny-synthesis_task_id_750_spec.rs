pub fn AddTupleToList(l: Seq<(int, int)>, t: (int, int)) -> (r: Seq<(int, int)>)
    ensures
        r.len() == l.len() + 1,
        r[r.len() - 1] == t,
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[i],
{
}