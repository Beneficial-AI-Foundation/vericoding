pub fn torneo(valores: &[f64], i: usize, j: usize, k: usize) -> (pos_padre: usize, pos_madre: usize)
    requires(
        valores.len() >= 20 && valores.len() < 50 && 
        i < valores.len() && j < valores.len() && k < valores.len() && 
        i != j && j != k && k != i
    )
    ensures(|result: (usize, usize)| {
        let (pos_padre, pos_madre) = result;
        exists|p: usize, q: usize, r: usize| {
            &&& (p == i || p == j || p == k)
            &&& (q == i || q == j || q == k) 
            &&& (r == i || r == j || r == k)
            &&& p != q && q != r && p != r
            &&& valores[p] >= valores[q] && valores[q] >= valores[r]
            &&& pos_padre == p && pos_madre == q
        }
    })
{
}