//IMPL 
method main(n: int) returns(x: int, m: int)
requires n > 0
ensures (n <= 0) || (0 <= m && m < n)
{
    x := 0;
    m := 0;
    /* code modified by LLM (iteration 1): added assertion to help verify postcondition */
    assert 0 <= m && m < n;
}