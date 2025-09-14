

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q // Q
// </vc-spec>
// <vc-code>
{
  var S := {i, j, k};
  var pos_otro:int;

  if Valores[i] >= Valores[j] {
    if Valores[i] >= Valores[k] {
      pos_padre := i;
      if Valores[j] >= Valores[k] {
        pos_madre := j;
        pos_otro := k;
        assert Valores[pos_padre] >= Valores[pos_madre];
        assert Valores[pos_madre] >= Valores[pos_otro];
        assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
      } else {
        pos_madre := k;
        pos_otro := j;
        assert Valores[pos_padre] >= Valores[pos_madre];
        assert Valores[pos_madre] >= Valores[pos_otro];
        assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
      }
    } else {
      pos_padre := k;
      pos_madre := i;
      pos_otro := j;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[pos_otro];
      assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
    }
  } else {
    if Valores[j] >= Valores[k] {
      pos_padre := j;
      if Valores[i] >= Valores[k] {
        pos_madre := i;
        pos_otro := k;
        assert Valores[pos_padre] >= Valores[pos_madre];
        assert Valores[pos_madre] >= Valores[pos_otro];
        assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
      } else {
        pos_madre := k;
        pos_otro := i;
        assert Valores[pos_padre] >= Valores[pos_madre];
        assert Valores[pos_madre] >= Valores[pos_otro];
        assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
      }
    } else {
      pos_padre := k;
      pos_madre := j;
      pos_otro := i;
      assert Valores[pos_padre] >= Valores[pos_madre];
      assert Valores[pos_madre] >= Valores[pos_otro];
      assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
    }
  }

  assert pos_padre in S && pos_madre in S && pos_otro in S;
  assert Valores[pos_padre] >= Valores[pos_madre] && Valores[pos_madre] >= Valores[pos_otro];
  assert pos_padre != pos_madre && pos_madre != pos_otro && pos_padre != pos_otro;
}
// </vc-code>

