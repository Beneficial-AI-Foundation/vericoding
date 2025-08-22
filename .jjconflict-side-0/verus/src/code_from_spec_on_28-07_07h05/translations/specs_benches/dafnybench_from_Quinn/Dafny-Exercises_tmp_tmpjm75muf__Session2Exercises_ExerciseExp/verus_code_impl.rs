decreases e
{
    if e >= 0 then
        if e == 0 then 1 else x * exp(x, e - 1)
    else
        0
}

//IMPL exp_positive_property
lemma exp_positive_property(x: int, e: int)
    requires x > 0 && e >= 0
    ensures exp(x, e) > 0
    decreases e
{
    if e == 0 {
        /* code modified by LLM (iteration 1): added explicit assertion for base case */
        assert exp(x, 0) == 1;
    } else {
        /* code modified by LLM (iteration 1): added inductive reasoning */
        exp_positive_property(x, e - 1);
        assert exp(x, e - 1) > 0;
        assert exp(x, e) == x * exp(x, e - 1);
        assert x > 0 && exp(x, e - 1) > 0;
    }
}

//IMPL exp3_lemma
lemma exp3_lemma(n: int) 
    requires n >= 1
    ensures (exp(3, n) - 1) % 2 == 0
    decreases n
{
    if n == 1 {
        /* code modified by LLM (iteration 1): added base case verification */
        assert exp(3, 1) == 3;
        assert (3 - 1) % 2 == 0;
    } else {
        /* code modified by LLM (iteration 1): added inductive step reasoning */
        exp3_lemma(n - 1);
        assert (exp(3, n - 1) - 1) % 2 == 0;
        assert exp(3, n) == 3 * exp(3, n - 1);
        assert (exp(3, n) - 1) == 3 * exp(3, n - 1) - 1;
        assert (exp(3, n) - 1) == 3 * (exp(3, n - 1) - 1) + 2;
        assert 3 % 2 == 1;
        assert 2 % 2 == 0;
        assert (3 * (exp(3, n - 1) - 1)) % 2 == 0;
        assert (3 * (exp(3, n - 1) - 1) + 2) % 2 == 0;
    }
}

/* code modified by LLM (iteration 1): added helper lemma for exponent properties */
lemma exp_add_lemma(x: int, a: int, b: int)
    requires a >= 0 && b >= 0
    ensures exp(x, a + b) == exp(x, a) * exp(x, b)
    decreases a
{
    if a == 0 {
        assert exp(x, 0) == 1;
        assert exp(x, 0 + b) == exp(x, b);
        assert 1 * exp(x, b) == exp(x, b);
    } else {
        exp_add_lemma(x, a - 1, b);
        assert exp(x, (a - 1) + b) == exp(x, a - 1) * exp(x, b);
        assert a + b == (a - 1) + b + 1;
        assert exp(x, a + b) == x * exp(x, (a + b) - 1);
        assert exp(x, (a + b) - 1) == exp(x, (a - 1) + b);
        assert exp(x, a + b) == x * exp(x, a - 1) * exp(x, b);
        assert exp(x, a) == x * exp(x, a - 1);
    }
}

//IMPL mult8_lemma
lemma mult8_lemma(n: int)
    requires n >= 1
    ensures (exp(3, 2 * n) - 1) % 8 == 0
    decreases n
{
    if n == 1 {
        /* code modified by LLM (iteration 1): added explicit computation for exp(3, 2) */
        assert exp(3, 2) == 3 * exp(3, 1);
        assert exp(3, 1) == 3 * exp(3, 0);
        assert exp(3, 0) == 1;
        assert exp(3, 1) == 3;
        assert exp(3, 2) == 9;
        assert (9 - 1) % 8 == 0;
    } else {
        /* code modified by LLM (iteration 1): added inductive step with helper lemma */
        mult8_lemma(n - 1);
        assert (exp(3, 2 * (n - 1)) - 1) % 8 == 0;
        assert 2 * n == 2 * (n - 1) + 2;
        exp_add_lemma(3, 2 * (n - 1), 2);
        assert exp(3, 2 * n) == exp(3, 2 * (n - 1) + 2);
        assert exp(3, 2 * (n - 1) + 2) == exp(3, 2 * (n - 1)) * exp(3, 2);
        assert exp(3, 2) == 9;
        assert exp(3, 2 * n) == 9 * exp(3, 2 * (n - 1));
        assert (exp(3, 2 * n) - 1) == 9 * exp(3, 2 * (n - 1)) - 1;
        assert (exp(3, 2 * n) - 1) == 9 * (exp(3, 2 * (n - 1)) - 1) + 8;
        assert 8 % 8 == 0;
        assert (9 * (exp(3, 2 * (n - 1)) - 1)) % 8 == 0;
        assert (9 * (exp(3, 2 * (n - 1)) - 1) + 8) % 8 == 0;
    }
}