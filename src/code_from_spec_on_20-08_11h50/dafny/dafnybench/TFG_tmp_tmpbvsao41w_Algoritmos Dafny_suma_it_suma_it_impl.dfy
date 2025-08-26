// <vc-helpers>
lemma suma_vector_split(V: array<int>, i: nat, j: nat)
    requires 0 <= i <= j <= V.Length
    ensures suma_vector(V, i) == suma_partial(V, i, j) + suma_vector(V, j)
    decreases j - i
{
    if i == j {
        // Base case: suma_vector(V, i) == 0 + suma_vector(V, i)
    } else {
        // Inductive case
        suma_vector_split(V, i + 1, j);
    }
}

function suma_partial(V: array<int>, start: nat, end: nat): int
    requires 0 <= start <= end <= V.Length
    reads V
    decreases end - start
{
    if start == end then 0
    else V[start] + suma_partial(V, start + 1, end)
}

lemma suma_partial_equiv(V: array<int>, i: nat)
    requires 0 <= i <= V.Length
    ensures suma_partial(V, 0, i) == suma_iterative_equiv(V, i)
    decreases i
{
    if i == 0 {
        // Base case: both are 0
        assert suma_partial(V, 0, 0) == 0;
        assert suma_iterative_equiv(V, 0) == 0;
    } else {
        // Inductive case
        suma_partial_equiv(V, i - 1);
        // suma_partial(V, 0, i) == V[0] + suma_partial(V, 1, i)
        // suma_iterative_equiv(V, i) == suma_iterative_equiv(V, i-1) + V[i-1]
        // We need to show suma_partial(V, 1, i) == suma_iterative_equiv(V, i-1) + V[i-1] - V[0]
        // Actually, let's show the relationship more carefully
        assert suma_partial(V, 0, i) == V[0] + suma_partial(V, 1, i);
        assert suma_iterative_equiv(V, i) == suma_iterative_equiv(V, i - 1) + V[i - 1];
        
        // We need a helper to show suma_partial(V, 1, i) relates to suma_iterative_equiv
        suma_partial_shift_equiv(V, 1, i);
    }
}

lemma suma_partial_shift_equiv(V: array<int>, start: nat, end: nat)
    requires 0 <= start <= end <= V.Length
    ensures suma_partial(V, start, end) == suma_iterative_equiv_range(V, start, end)
    decreases end - start
{
    if start == end {
        assert suma_partial(V, start, end) == 0;
        assert suma_iterative_equiv_range(V, start, end) == 0;
    } else {
        suma_partial_shift_equiv(V, start + 1, end);
    }
}

function suma_iterative_equiv_range(V: array<int>, start: nat, end: nat): int
    requires 0 <= start <= end <= V.Length
    reads V
    decreases end - start
{
    if start == end then 0
    else suma_iterative_equiv_range(V, start, end - 1) + V[end - 1]
}

function suma_iterative_equiv(V: array<int>, i: nat): int
    requires 0 <= i <= V.Length
    reads V
    decreases i
{
    if i == 0 then 0
    else suma_iterative_equiv(V, i - 1) + V[i - 1]
}

lemma iterative_sum_correct(V: array<int>, i: nat)
    requires 0 <= i <= V.Length
    ensures suma_iterative_equiv(V, i) + suma_vector(V, i) == suma_vector(V, 0)
    decreases V.Length - i
{
    if i == V.Length {
        // Base case: suma_iterative_equiv(V, V.Length) + suma_vector(V, V.Length) == suma_vector(V, 0)
        // suma_vector(V, V.Length) == 0
        assert suma_vector(V, V.Length) == 0;
        // suma_iterative_equiv(V, V.Length) should equal suma_vector(V, 0)
        iterative_equiv_is_vector_sum(V, V.Length);
    } else {
        // Inductive case
        iterative_sum_correct(V, i + 1);
        // We know: suma_iterative_equiv(V, i+1) + suma_vector(V, i+1) == suma_vector(V, 0)
        // We want: suma_iterative_equiv(V, i) + suma_vector(V, i) == suma_vector(V, 0)
        // suma_iterative_equiv(V, i+1) == suma_iterative_equiv(V, i) + V[i]
        // suma_vector(V, i) == V[i] + suma_vector(V, i+1)
        assert suma_iterative_equiv(V, i + 1) == suma_iterative_equiv(V, i) + V[i];
        assert suma_vector(V, i) == V[i] + suma_vector(V, i + 1);
    }
}

lemma iterative_equiv_is_vector_sum(V: array<int>, n: nat)
    requires 0 <= n <= V.Length
    ensures suma_iterative_equiv(V, n) == suma_vector(V, 0) - suma_vector(V, n)
    decreases n
{
    if n == 0 {
        assert suma_iterative_equiv(V, 0) == 0;
        assert suma_vector(V, 0) - suma_vector(V, 0) == 0;
    } else {
        iterative_equiv_is_vector_sum(V, n - 1);
        assert suma_iterative_equiv(V, n) == suma_iterative_equiv(V, n - 1) + V[n - 1];
        assert suma_vector(V, n - 1) == V[n - 1] + suma_vector(V, n);
    }
}
// </vc-helpers>

// <vc-spec>
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
// </vc-spec>
// <vc-code>
{
    x := 0;
    var i := 0;
    
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant x == suma_iterative_equiv(V, i)
        decreases V.Length - i
    {
        x := x + V[i];
        i := i + 1;
    }
    
    // At this point i == V.Length and x == suma_iterative_equiv(V, V.Length)
    iterative_sum_correct(V, V.Length);
    suma_partial_equiv(V, i);
    assert x == suma_vector(V, 0);
}
// </vc-code>

function suma_vector(V: array<int>, n: nat): int

// x = V[n] + V[n + 1] + ... + V[N - 1]
// Funcion auxiliar para la suma de
// las componentes de un vector

    requires 0 <= n <= V.Length  
    decreases V.Length - n  
    reads V  
{    
    if (n == V.Length) then 0 
    else V[n] + suma_vector(V, n + 1)  
}