//ATOM valid_base
predicate valid_base(b : nat) {
 b >= 2
}

//ATOM nitness
predicate nitness(b : nat, n : nat)
 requires (valid_base(b))
{
 0 <= n < b
}

//ATOM is_max_nit
predicate is_max_nit(b : nat, q : nat) {
 q == b - 1
}

//IMPL max_nit
method max_nit(b: nat) returns (nmax : nat)
 requires (valid_base(b))
 ensures (nitness(b, nmax))
 ensures (is_max_nit(b, nmax))
{
 /* code modified by LLM (iteration 1): fixed implementation to properly satisfy both postconditions */
 nmax := b - 1;
 
 /* code modified by LLM (iteration 1): added assertion to help Dafny verify nitness postcondition */
 assert nmax == b - 1;
 assert valid_base(b);
 assert b >= 2;
 assert 0 <= nmax;
 assert nmax < b;
}