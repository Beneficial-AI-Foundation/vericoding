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
lemma RowColumnProductFromAdditive(m1: array2<int>, m2: array2<int>, row: nat, column: nat, i: nat, n: nat)
    requires m1 != null && m2 != null && i <= n <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures RowColumnProductFrom(m1, m2, row, column, i) == RowColumnProductFromHelper(m1, m2, row, column, i, n) + RowColumnProductFrom(m1, m2, row, column, n)
    decreases n - i
{
    if i < n {
        assert RowColumnProductFrom(m1, m2, row, column, i) == m1[row,i]*m2[i,column] + RowColumnProductFrom(m1, m2, row, column, i+1);
        RowColumnProductFromAdditive(m1, m2, row, column, i+1, n);
        assert RowColumnProductFromHelper(m1, m2, row, column, i, n) == m1[row,i]*m2[i,column] + RowColumnProductFromHelper(m1, m2, row, column, i+1, n);
    }
}

ghost function RowColumnProductFromHelper(m1: array2<int>, m2: array2<int>, row: nat, column: nat, start: nat, end: nat): int
    reads m1
    reads m2
    requires m1 != null && m2 != null && start <= end <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases end - start
{
    if start == end then
        0
    else
        m1[row,start]*m2[start,column] + RowColumnProductFromHelper(m1, m2, row, column, start+1, end)
}

lemma RowColumnProductFromSameAsHelperFunction(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat)
    requires m1 != null && m2 != null && k <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures RowColumnProductFrom(m1, m2, row, column, k) == RowColumnProductFromHelper(m1, m2, row, column, k, m1.Length1)
    decreases m1.Length1 - k
{
    if k < m1.Length1 {
        RowColumnProductFromSameAsHelperFunction(m1, m2, row, column, k+1);
        assert RowColumnProductFromHelper(m1, m2, row, column, k, m1.Length1) == m1[row,k]*m2[k,column] + RowColumnProductFromHelper(m1, m2, row, column, k+1, m1.Length1);
    }
}

lemma RowColumnProductFromHelperAdditive(m1: array2<int>, m2: array2<int>, row: nat, column: nat, start: nat, mid: nat, end: nat)
    requires m1 != null && m2 != null && start <= mid <= end <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures RowColumnProductFromHelper(m1, m2, row, column, start, end) == RowColumnProductFromHelper(m1, m2, row, column, start, mid) + RowColumnProductFromHelper(m1, m2, row, column, mid, end)
    decreases end - start
{
    if start < mid {
        RowColumnProductFromHelperAdditive(m1, m2, row, column, start+1, mid, end);
    }
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
    var x := 0;
    while x < m1.Length0
        invariant 0 <= x <= m1.Length0
        invariant m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
        invariant forall i, j | 0 <= i < x && 0 <= j < m3.Length1 :: m3[i, j] == RowColumnProduct(m1, m2, i, j)
    {
        var y := 0;
        while y < m2.Length1
            invariant 0 <= y <= m2.Length1
            invariant forall j | 0 <= j < y :: m3[x, j] == RowColumnProduct(m1, m2, x, j)
            invariant forall i, j | 0 <= i < x && 0 <= j < m3.Length1 :: m3[i, j] == RowColumnProduct(m1, m2, i, j)
        {
            m3[x, y] := 0;
            var z := 0;
            while z < m1.Length1
                invariant 0 <= z <= m1.Length1
                invariant m3[x, y] == RowColumnProductFromHelper(m1, m2, x, y, 0, z)
                invariant forall j | 0 <= j < y :: m3[x, j] == RowColumnProduct(m1, m2, x, j)
                invariant forall i, j | 0 <= i < x && 0 <= j < m3.Length1 :: m3[i, j] == RowColumnProduct(m1, m2, i, j)
            {
                RowColumnProductFromHelperAdditive(m1, m2, x, y, 0, z, z+1);
                m3[x, y] := m3[x, y] + m1[x, z] * m2[z, y];
                z := z + 1;
            }
            RowColumnProductFromSameAsHelperFunction(m1, m2, x, y, 0);
            assert RowColumnProduct(m1, m2, x, y) == RowColumnProductFromHelper(m1, m2, x, y, 0, m1.Length1);
            y := y + 1;
        }
        x := x + 1;
    }
}
// </vc-code>

