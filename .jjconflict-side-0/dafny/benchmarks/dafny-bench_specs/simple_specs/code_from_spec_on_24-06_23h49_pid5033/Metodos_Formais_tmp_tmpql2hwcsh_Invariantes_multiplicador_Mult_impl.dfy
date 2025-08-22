//IMPL 
// Exemplo de invariantes
// Invariante significa que o valor não muda desde a pré-condição até a pós-condição

method Mult(x:nat, y:nat) returns (r:nat)
ensures r == x * y
{
    r := x * y;
}