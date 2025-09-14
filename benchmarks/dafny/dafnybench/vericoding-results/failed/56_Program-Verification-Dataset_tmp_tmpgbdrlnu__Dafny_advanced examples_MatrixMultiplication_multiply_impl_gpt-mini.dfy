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
// No helper lemmas required.
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
  var n0 := m1.Length0;
  var n1 := m1.Length1; // equals m2.Length0
  var n2 := m2.Length1;
  m3 := new int[n0, n2];
  var i := 0;
  while i < n0
    invariant 0 <= i <= n0
    invariant n0 == m1.Length0 && n1 == m1.Length1 && n2 == m2.Length1
    invariant forall ii, jj | 0 <= ii < i && 0 <= jj < n2 :: m3[ii, jj] == RowColumnProduct(m1, m2, ii, jj)
    decreases n0 - i
  {
    var row := i;
    var j := 0;
    while j < n2
      invariant 0 <= j <= n2
      invariant row == i && 0 <= row < n0
      invariant n0 == m1.Length0 && n1 == m1.Length1 && n2 == m2.Length1
      invariant forall jj | 0 <= jj < j :: m3[row, jj] == RowColumnProduct(m1, m2, row, jj)
      decreases n2 - j
    {
      var s := 0;
      var k := 0;
      while k < n1
        invariant 0 <= k <= n1
        invariant n0 == m1.Length0 && n1 == m1.Length1 && n2 == m2.Length1
        invariant s == RowColumnProductFrom(m1, m2, row, j, 0) - RowColumnProductFrom(m1, m2, row, j, k)
        decreases n1 - k
      {
        s := s + m1[row, k] * m2[k, j];
        k := k + 1;
      }
      m3[row, j] := s;
      j := j + 1;
    }
    assert forall jj | 0 <= jj < n2 :: m3[row, jj] == RowColumnProduct(m1, m2, row, jj);
    assert forall ii, jj | 0 <= ii < i+1 && 0 <= jj < n2 ::
      m3[ii, jj] == RowColumnProduct(m1, m2, ii, jj);
    i := i + 1;
  }
  return m3;
}
// </vc-code>

