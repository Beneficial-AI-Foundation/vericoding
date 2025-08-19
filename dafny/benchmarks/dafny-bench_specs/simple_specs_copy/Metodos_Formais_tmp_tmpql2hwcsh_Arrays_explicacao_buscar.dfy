// SPEC
// Array<T> = visualização de um array
// Uma busca ordenada em um array
// Buscar: Array<Z>xZ -> Z (Z é inteiro)
// Pré: True (pré-condição é sempre verdadeira)
// Pos: R < 0 => Para todo i pertencente aos naturais(0 <= i < A.length => A[i] != X) e
// 0 <= R < A.length => A[R] = x 
//
// método em qualquer linguagem:
// R = 0
// Enquanto(R < |A|) {
}
// retorne -1 
// 
// X | R | |A|
// 10 | 0 | 5
// 10 | 1 | 5
// 10 | 2 | 
// invariante detectada: 0 <= R <= |A| e Para todo i pertencente aos naturais(0 <= i < R => A[i] != X)

// no dafy
// forall = é o para todo logico
// :: é igual ao tal que lógico
// ==> é o então lógico
// forall i :: 0 <= i < a.Length ==> a[i] != x (para todo i tal que i e maior ou igual a zero e menor que o tamanho do array, então a posição i do array a é diferente de x)

method buscar(a:array<int>, x:int) returns (r:int)
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
  ensures 0 <= r < a.Length ==> a[r] == x
{
}
