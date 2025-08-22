// SPEC
method torneo(Valores : array?<real>, i : int, j : int, k : int) returns (pos_padre : int, pos_madre : int)
  requires Valores != null && Valores.Length >= 20 && Valores.Length < 50 && i >= 0 && j >= 0 && k >= 0 
  requires i < Valores.Length && j < Valores.Length && k < Valores.Length && i != j && j != k && k != i 
  ensures exists p, q, r | p in {
}

{
}
