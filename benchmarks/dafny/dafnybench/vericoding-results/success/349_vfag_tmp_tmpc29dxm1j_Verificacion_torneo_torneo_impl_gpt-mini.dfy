

// <vc-helpers>
// No additional helper code required.
// </vc-helpers>

// <vc-spec>
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q
// </vc-spec>
// <vc-code>
{
  var vi := Valores[i];
  var vj := Valores[j];
  var vk := Valores[k];

  if vi >= vj && vi >= vk {
    pos_padre := i;
    if vj >= vk {
      pos_madre := j;
      var rIdx := k;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    } else {
      pos_madre := k;
      var rIdx := j;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    }
  } else if vj >= vi && vj >= vk {
    pos_padre := j;
    if vi >= vk {
      pos_madre := i;
      var rIdx := k;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    } else {
      pos_madre := k;
      var rIdx := i;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    }
  } else {
    pos_padre := k;
    if vi >= vj {
      pos_madre := i;
      var rIdx := j;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    } else {
      pos_madre := j;
      var rIdx := i;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[rIdx];
      assert pos_padre in {i, j, k} && pos_madre in {i, j, k} && rIdx in {i, j, k};
      assert pos_padre != pos_madre && pos_madre != rIdx && pos_padre != rIdx;
      assert exists p, q, r :: p == pos_padre && q == pos_madre && r == rIdx && p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r && Valores[p] >= Valores[q] && Valores[q] >= Valores[r];
    }
  }
}
// </vc-code>

