function RowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
{
    RowColumnProductFrom(m1, m2, row, column, 0)
}

function RowColumnProductFrom(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases m1.Length1 - k
{
    if k == m1.Length1 then
        0
    else
        m1[row,k]*m2[k,column] + RowColumnProductFrom(m1, m2, row, column, k+1)
}

// <vc-helpers>
lemma RowColumnProductFromStep(m1: array2<int>, m2: array2<int>, i: nat, j: nat, k: nat)
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires i < m1.Length0 && j < m2.Length1
    requires k < m1.Length1
    ensures RowColumnProductFrom(m1, m2, i, j, k) == m1[i,k]*m2[k,j] + RowColumnProductFrom(m1, m2, i, j, k+1)
{
    // By definition of RowColumnProductFrom when k < m1.Length1
}

lemma RowColumnProductFromFinal(m1: array2<int>, m2: array2<int>, i: nat, j: nat)
    requires m1 != null && m2 != null && m1.Length1 == m2.Length0
    requires i < m1.Length0 && j < m2.Length1
    ensures RowColumnProductFrom(m1, m2, i, j, m1.Length1) == 0
{
    // By definition of RowColumnProductFrom when k == m1.Length1
}
// </vc-helpers>

// <vc-spec>
method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
// </vc-spec>
// <vc-code>
{
    m3 := new int[m1.Length0, m2.Length1];
    for i := 0 to m1.Length0
        invariant forall i0, j | 0 <= i0 < i && 0 <= j < m2.Length1 :: m3[i0, j] == RowColumnProduct(m1, m2, i0, j)
    {
        for j := 0 to m2.Length1
            invariant forall j0 | 0 <= j0 < j :: m3[i, j0] == RowColumnProduct(m1, m2, i, j0)
        {
            var sum := 0;
            for k := 0 to m1.Length1
                invariant sum == RowColumnProductFrom(m1, m2, i, j, 0) - RowColumnProductFrom(m1, m2, i, j, k)
            {
                sum := sum + m1[i,k] * m2[k,j];
                if k < m1.Length1 {
                    RowColumnProductFromStep(m1, m2, i, j, k);
                    assert sum == RowColumnProductFrom(m1, m2, i, j, 0) - RowColumnProductFrom(m1, m2, i, j, k+1);
                }
            }
            RowColumnProductFromFinal(m1, m2, i, j);
            assert sum == RowColumnProductFrom(m1, m2, i, j, 0) - RowColumnProductFrom(m1, m2, i, j, m1.Length1);
            assert sum == RowColumnProductFrom(m1, m2, i, j, 0);
            assert sum == RowColumnProduct(m1, m2, i, j);
            m3[i,j] := sum;
        }
    }
}
// </vc-code>

