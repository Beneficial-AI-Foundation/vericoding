//IMPL 
method LastDigit(n: int) returns (d: int)
    requires n >= 0
    ensures 0 <= d < 10
    ensures n % 10 == d
{
    /* code modified by LLM (iteration 2): added assert to help Dafny verify modulo range property */
    d := n % 10;
    assert 0 <= d < 10;
}