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
lemma RowColumnProductFromCorrect(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k: nat, k_final: nat)
    requires m1 != null && m2 != null && k <= k_final <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures RowColumnProductFrom(m1, m2, row, column, k) == CalcRowColumnProduct(m1, m2, row, column, k, k_final)
{
    if k == k_final then
        assert RowColumnProductFrom(m1, m2, row, column, k) == 0;
        assert CalcRowColumnProduct(m1, m2, row, column, k, k_final) == 0;
    else
        RowColumnProductFromCorrect(m1, m2, row, column, k+1, k_final);
        assert RowColumnProductFrom(m1, m2, row, column, k) == m1[row,k]*m2[k,column] + RowColumnProductFrom(m1, m2, row, column, k+1);
        assert CalcRowColumnProduct(m1, m2, row, column, k, k_final) == m1[row,k]*m2[k,column] + CalcRowColumnProduct(m1, m2, row, column, k+1, k_final);
    }

function CalcRowColumnProduct(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k_start: nat, k_end: nat): int
    reads m1, m2
    requires m1 != null && m2 != null && k_start <= k_end <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    decreases k_end - k_start
{
    if k_start == k_end then
        0
    else
        m1[row, k_start] * m2[k_start, column] + CalcRowColumnProduct(m1, m2, row, column, k_start + 1, k_end)
}


lemma CalcRowColumnProductSumProperty(m1: array2<int>, m2: array2<int>, row: nat, column: nat, k_start: nat, k_end: nat)
    requires m1 != null && m2 != null && k_start <= k_end <= m1.Length1 == m2.Length0
    requires row < m1.Length0 && column < m2.Length1
    ensures CalcRowColumnProduct(m1,m2,row,column,k_start,k_end) == (if k_start < k_end then m1[row,k_start]*m2[k_start,column] + CalcRowColumnProduct(m1,m2,row,column,k_start+1,k_end) else 0)
{
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
    var m := m1.Length0;
    var n := m1.Length1;
    var p := m2.Length1;

    m3 := new array2<int>(m, p);

    var i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant m3 != null && m3.Length0 == m && m3.Length1 == p
        invariant forall row, col | 0 <= row < i && 0 <= col < p ::
            m3[row, col] == RowColumnProduct(m1, m2, row, col)
    {
        var j := 0;
        while j < p
            invariant 0 <= j <= p
            invariant 0 <= i < m
            invariant m3 != null && m3.Length0 == m && m3.Length1 == p
            invariant forall row, col | 0 <= row < i && 0 <= col < p ::
                m3[row, col] == RowColumnProduct(m1, m2, row, col)
            invariant forall col | 0 <= col < j ::
                m3[i, col] == RowColumnProduct(m1, m2, i, col)
        {
            var sum := 0;
            var k := 0;
            while k < n
                invariant 0 <= k <= n
                invariant 0 <= i < m && 0 <= j < p
                invariant sum == CalcRowColumnProduct(m1, m2, i, j, 0, k)
            {
                sum := sum + m1[i, k] * m2[k, j];
                k := k + 1;
            }
            // After the loop, k == n
            // We need to prove sum == RowColumnProduct(m1, m2, i, j)
            // Which means sum == RowColumnProductFrom(m1, m2, i, j, 0)
            // And sum == CalcRowColumnProduct(m1, m2, i, j, 0, n)
            // So we need to show RowColumnProductFrom(m1, m2, i, j, 0) == CalcRowColumnProduct(m1, m2, i, j, 0, n)
            assert sum == CalcRowColumnProduct(m1, m2, i, j, 0, n); // This is true by invariant
            // Call the lemma to connect RowColumnProductFrom and CalcRowColumnProduct
            RowColumnProductFromCorrect(m1, m2, i, j, 0, n);
            assert RowColumnProductFrom(m1, m2, i, j, 0) == CalcRowColumnProduct(m1, m2, i, j, 0, n);
            assert sum == RowColumnProduct(m1, m2, i, j); // This is what we need for the postcondition

            m3[i, j] := sum;
            j := j + 1;
        }
        i := i + 1;
    }
    return m3;
}
// </vc-code>

