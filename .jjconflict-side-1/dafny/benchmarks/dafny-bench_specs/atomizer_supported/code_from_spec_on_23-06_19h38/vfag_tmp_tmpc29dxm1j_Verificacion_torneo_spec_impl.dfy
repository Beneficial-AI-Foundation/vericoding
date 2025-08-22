//IMPL torneo
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
    requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
    requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
    ensures exists p, q, r | p in {i, j, k} && q in {i, j, k} && r in {i, j, k} && p != q && q != r && p != r :: Valores[p] >= Valores[q] >= Valores[r] && pos_padre == p && pos_madre == q
{
    if Valores[i] >= Valores[j] && Valores[i] >= Valores[k] {
        // i is the largest
        if Valores[j] >= Valores[k] {
            pos_padre := i;
            pos_madre := j;
        } else {
            pos_padre := i;
            pos_madre := k;
        }
    } else if Valores[j] >= Valores[i] && Valores[j] >= Valores[k] {
        // j is the largest
        if Valores[i] >= Valores[k] {
            pos_padre := j;
            pos_madre := i;
        } else {
            pos_padre := j;
            pos_madre := k;
        }
    } else {
        // k is the largest
        if Valores[i] >= Valores[j] {
            pos_padre := k;
            pos_madre := i;
        } else {
            pos_padre := k;
            pos_madre := j;
        }
    }
}