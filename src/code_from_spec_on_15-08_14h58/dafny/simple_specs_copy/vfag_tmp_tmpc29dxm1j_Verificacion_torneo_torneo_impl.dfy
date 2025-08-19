//IMPL
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
  requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
  requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
  ensures pos_padre >= 0 && pos_padre < Valores.Length
  ensures pos_madre >= 0 && pos_madre < Valores.Length
  ensures pos_padre != pos_madre
{
    // Tournament selection: compare the three candidates and select two winners
    if Valores[i] >= Valores[j] && Valores[i] >= Valores[k] {
        // i has the highest value
        pos_padre := i;
        if Valores[j] >= Valores[k] {
            pos_madre := j;
        } else {
            pos_madre := k;
        }
    } else if Valores[j] >= Valores[i] && Valores[j] >= Valores[k] {
        // j has the highest value
        pos_padre := j;
        if Valores[i] >= Valores[k] {
            pos_madre := i;
        } else {
            pos_madre := k;
        }
    } else {
        // k has the highest value
        pos_padre := k;
        if Valores[i] >= Valores[j] {
            pos_madre := i;
        } else {
            pos_madre := j;
        }
    }
}