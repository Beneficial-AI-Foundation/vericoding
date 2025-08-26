// The `soma` function is defined recursively:
// - `soma(a, 0) = 0` (base case)
// - `soma(a, i) = a[i-1] + soma(a, i-1)` for `i > 0`

// So `soma(a, a.Length)` computes the sum of all elements from index 0 to `a.Length-1`.

// I need to implement this iteratively in the method. I'll use a loop that accumulates the sum:

// Deve ser criado uma função explicando o que é um somatório
// Somatorio: Array<N> -> N
// Pre: True
// Pos: Somatorio(A) = somatório de i = 0 até |A|-1 os valores das posições do array pelo i
//

// function é uma fórmula matemática, ele não possui variaveis globais
// Soma: Array<N>xN -> N
// { Soma(A,0) = A[0]
// { Soma(A,i) = A[i] + soma(A, i-1) , se i > 0
// Teste
// |A| = 4
// Soma(A, |A|-1) = Soma(A,3)
// A[3] + Soma(A,2)
// A[3] + A[2] + Soma(A,1)
// A[3] + A[2] + A[1] + Soma(A,0)
// A[3] + A[2] + A[1] + A[0]
// <vc-spec>
function soma(a:array<nat>, i:nat):nat
    requires i <= a.Length //Tem que dizer que o i só vai até um valor antes do tamanho do array
    reads a //serve para dizer que está sendo lido da memoria o array a (áreas de memória)
{
    if i == 0
    then 0
    else a[i-1] + soma(a,i-1)
}

// <vc-helpers>
// </vc-helpers>

method somatorio(a:array<nat>) returns (s:nat)
    ensures s == soma(a, a.Length)
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == soma(a, i)
  {
    s := s + a[i];
    i := i + 1;
  }
}
// </vc-code>