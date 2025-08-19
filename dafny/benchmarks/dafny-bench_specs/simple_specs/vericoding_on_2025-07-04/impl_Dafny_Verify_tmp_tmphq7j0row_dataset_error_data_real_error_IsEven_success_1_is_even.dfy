//ATOM
function even(n: int): bool
 requires n >= 0
{
 if n == 0 then true else !even(n-1)
}

//IMPL 
/* code modified by LLM (iteration 2): fixed lemma to properly prove equivalence with correct inductive reasoning */
lemma even_equiv_mod(n: int)
 requires n >= 0
 ensures even(n) <==> (n % 2 == 0)
{
 if n == 0 {
   // Base case: even(0) == true and 0 % 2 == 0
 } else if n == 1 {
   // Base case: even(1) == false and 1 % 2 == 1
 } else {
   // Inductive case: even(n) == !even(n-1) and we need to relate this to modular arithmetic
   even_equiv_mod(n-1);
   // Now we know even(n-1) <==> ((n-1) % 2 == 0)
   // Since even(n) == !even(n-1), we have:
   // even(n) <==> !((n-1) % 2 == 0) <==> ((n-1) % 2 == 1) <==> (n % 2 == 0)
 }
}

method is_even(n: int) returns (r: bool)
 requires n >= 0
 ensures r <==> even(n)
{
    /* code modified by LLM (iteration 2): added lemma call to establish equivalence */
    even_equiv_mod(n);
    r := n % 2 == 0;
}