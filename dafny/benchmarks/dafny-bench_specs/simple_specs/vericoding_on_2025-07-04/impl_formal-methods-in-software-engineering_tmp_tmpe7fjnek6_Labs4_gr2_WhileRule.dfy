//IMPL
method WhileRule()
{
    var i := 0;
    var sum := 0;
    
    while i < 10
        invariant 0 <= i <= 10
        invariant sum == i * (i - 1) / 2
    {
        sum := sum + i;
        i := i + 1;
    }
    
    assert i == 10;
    assert sum == 45;
}