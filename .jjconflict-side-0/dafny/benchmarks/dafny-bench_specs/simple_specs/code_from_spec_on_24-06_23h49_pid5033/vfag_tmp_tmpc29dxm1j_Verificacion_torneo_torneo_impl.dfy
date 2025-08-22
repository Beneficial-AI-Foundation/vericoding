//IMPL 
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
  requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
  requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
  ensures pos_padre in {i, j, k} && pos_madre in {i, j, k} && pos_padre != pos_madre
  ensures Valores[pos_padre] >= Valores[pos_madre]
  ensures forall idx :: idx in {i, j, k} ==> Valores[pos_padre] >= Valores[idx]
  ensures forall idx :: idx in {i, j, k} && idx != pos_padre ==> Valores[pos_madre] >= Valores[idx]
{
  // Find the position with maximum value
  if Valores[i] >= Valores[j] && Valores[i] >= Valores[k] {
    pos_padre := i;
    // Find second best between j and k
    if Valores[j] >= Valores[k] {
      pos_madre := j;
    } else {
      pos_madre := k;
    }
  } else if Valores[j] >= Valores[i] && Valores[j] >= Valores[k] {
    pos_padre := j;
    // Find second best between i and k
    if Valores[i] >= Valores[k] {
      pos_madre := i;
    } else {
      pos_madre := k;
    }
  } else {
    pos_padre := k;
    // Find second best between i and j
    if Valores[i] >= Valores[j] {
      pos_madre := i;
    } else {
      pos_madre := j;
    }
  }
}