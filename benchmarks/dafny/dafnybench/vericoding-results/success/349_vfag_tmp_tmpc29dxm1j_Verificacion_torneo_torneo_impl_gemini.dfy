// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
// </vc-spec>
// <vc-code>
{
  var vi := Valores[i];
  var vj := Valores[j];
  var vk := Valores[k];

  if vi >= vj {
    // vi >= vj
    if vi >= vk {
      // vi is max
      pos_padre := i;
      if vj >= vk {
        pos_madre := j;
      } else {
        pos_madre := k;
      }
    } else {
      // vk > vi >= vj. vk is max, vi is second.
      pos_padre := k;
      pos_madre := i;
    }
  } else {
    // vj > vi
    if vj >= vk {
      // vj is max
      pos_padre := j;
      if vi >= vk {
        pos_madre := i;
      } else {
        pos_madre := k;
      }
    } else {
      // vk > vj > vi. vk is max, vj is second.
      pos_padre := k;
      pos_madre := j;
    }
  }
}
// </vc-code>
