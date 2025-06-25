pub fn Maximum(values: Seq<int>) -> (max: int)
    requires
        values != seq![],
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values[i] <= max,
{
}

proof fn MaximumIsUnique(values: Seq<int>, m1: int, m2: int)
    requires
        values.contains(m1) && (forall|i: int| 0 <= i < values.len() ==> values[i] <= m1),
        values.contains(m2) && (forall|i: int| 0 <= i < values.len() ==> values[i] <= m2),
    ensures
        m1 == m2,
{
}