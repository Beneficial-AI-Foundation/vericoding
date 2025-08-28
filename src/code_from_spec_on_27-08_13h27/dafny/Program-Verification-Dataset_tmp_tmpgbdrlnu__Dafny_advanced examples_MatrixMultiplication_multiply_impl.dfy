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
function SumRowColumn(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat): int
    reads m1, m2
    requires k <= m1.Length1 && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases m1.Length1 - k
{
    if k == m1.Length1 then 0
    else m1[row, k] * m2[k, column] + SumRowColumn(m1, m2, row, column, k + 1)
}

lemma RowColumnProductCorrect(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat)
    requires k <= m1.Length1 && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures RowColumnProductFrom(m1, m2, row, column, k) == SumRowColumn(m1, m2, row, column, k)
    decreases m1.Length1 - k
{
    if k == m1.Length1 {
        assert RowColumnProductFrom(m1, m2, row, column, k) == 0;
        assert SumRowColumn(m1, m2, row, column, k) == 0;
    } else {
        calc {
            RowColumnProductFrom(m1, m2, row, column, k);
            == m1[row, k] * m2[k, column] + RowColumnProductFrom(m1, m2, row, column, k + 1);
            == { RowColumnProductCorrect(m1, m2, row, column, k + 1); }
               m1[row, k] * m2[k, column] + SumRowColumn(m1, m2, row, column, k + 1);
            == SumRowColumn(m1, m2, row, column, k);
        }
    }
}

lemma SumRowColumnUpdate(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat)
    requires 0 <= k <= m1.Length1 && m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures SumRowColumn(m1, m2, row, column, 0) == SumRowColumn(m1, m2, row, column, k) + SumRowColumn(m1, m2, row, column, 0) - SumRowColumn(m1, m2, row, column, k)
    decreases m1.Length1 - k
{
    if k == m1.Length1 {
        assert SumRowColumn(m1, m2, row, column, k) == 0;
    } else {
        assert SumRowColumn(m1, m2, row, column, 0) == m1[row, 0] * m2[0, column] + SumRowColumn(m1, m2, row, column, 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
// </vc-spec>
// </vc-spec>

// <vc-code>
method MatrixMultiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1.Length1 == m2.Length0
    ensures m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
{
    m3 := new int[m1.Length0, m2.Length1];
    var i := 0;
    while i < m1.Length0
        invariant 0 <= i <= m1.Length0
        invariant forall x, y | 0 <= x < i && 0 <= y < m2.Length1 ::
            m3[x, y] == RowColumnProduct(m1, m2, x, y)
    {
        var j := 0;
        while j < m2.Length1
            invariant 0 <= j <= m2.Length1
            invariant forall x, y | 0 <= x < i && 0 <= y < m2.Length1 ::
                m3[x, y] == RowColumnProduct(m1, m2, x, y)
            invariant forall y | 0 <= y < j ::
                m3[i, y] == RowColumnProduct(m1, m2, i, y)
        {
            var sum := 0;
            var k := 0;
            while k < m1.Length1
                invariant 0 <= k <= m1.Length1
                invariant sum == SumRowColumn(m1, m2, i, j, 0) - SumRowColumn(m1, m2, i, j, k)
            {
                sum := sum + m1[i, k] * m2[k, j];
                k := k + 1;
                if k < m1.Length1 {
                    assert sum == SumRowColumn(m1, m2, i, j, 0) - SumRowColumn(m1, m2, i, j, k);
                }
            }
            m3[i, j] := sum;
            assert k == m1.Length1;
            assert sum == SumRowColumn(m1, m2, i, j, 0);
            RowColumnProductCorrect(m1, m2, i, j, 0);
            assert m3[i, j] == RowColumnProduct(m1, m2, i, j);
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
