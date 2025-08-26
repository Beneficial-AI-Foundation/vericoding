// The specification requires that the method returns `suma_aux(V, 0)`, which according to the comment should be `V[0] + V[1] + ... + V[N-1]`.

// - Takes an array `V` and starting index `n`
// - Returns the sum from `V[n]` to `V[V.Length-1]`
// - Base case: when `n == V.Length`, returns 0
// - Recursive case: returns `V[n] + suma_aux(V, n+1)`

// So `suma_aux(V, 0)` will indeed compute the sum of all elements in the array.

// The implementation is straightforward - I just need to call `suma_aux(V, 0)` and return the result.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method suma_componentes(V : array?<int>) returns (suma : int)

  requires V != null
  ensures  suma == suma_aux(V, 0)   // x = V[0] + V[1] + ... + V[N - 1]
// </vc-spec>
// <vc-code>
{
  suma := suma_aux(V, 0);
}
// </vc-code>

function suma_aux(V : array?<int>, n : int) : int

  // suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]

  requires V != null            // P_0
  requires 0 <= n <= V.Length       // Q_0

  decreases V.Length - n        // C_0

  reads V

{

  if (n == V.Length) then 0                     // Caso base:      n = N
                     else V[n] + suma_aux(V, n + 1)     // Caso recursivo: n < N

}