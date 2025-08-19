//IMPL 
method Ceiling7(n:nat) returns (k:nat)
requires n >= 0
ensures k == n-(n%7)
{
    k := n - (n % 7);
}