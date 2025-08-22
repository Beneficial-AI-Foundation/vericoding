// ATOM 
ghost function power(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) > 0.0

// ATOM 
ghost function log(n: real, alpha: real): real
    requires n > 0.0 && alpha > 0.0
    ensures log(n, alpha) > 0.0

// ATOM 
lemma consistency(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures log(power(n,alpha), alpha) == n
    ensures power(log(n, alpha), alpha) == n
{
}

// ATOM 
lemma logarithmSum(n: real, alpha: real, x: real, y: real)
    requires n > 0.0 && alpha > 0.0
    requires x > 0.0
    requires n == x * y
    ensures log(n,alpha) == log(x, alpha) +  log(y, alpha)
{
}

// ATOM 
lemma powerLemma(n: real, alpha: real)
    requires n > 0.0 && alpha > 0.0
    ensures power(n, alpha) * alpha == power(n+1.0, alpha)
{
}

// ATOM 
lemma power1(alpha: real)
    requires alpha > 0.0
    ensures power(1.0, alpha) == alpha
{
}

// ATOM 
lemma test() {
    var pow3 := power(3.0,4.0);
    consistency(3.0,4.0);
    var log6 := log(6.0,8.0);
    logarithmSum(6.0, 8.0, 2.0, 3.0);
}

// ATOM 
lemma test2() {
    var pow3 := power(3.0, 4.0);
    var power4 := power(4.0, 4.0);
    powerLemma(3.0, 4.0);
}

// IMPL 
method pow(n: nat, alpha: real) returns (product: real)
    requires n > 0
    requires alpha > 0.0
    ensures product == power(n as real, alpha)
{
    /* code modified by LLM (iteration 1): Initialize product with alpha and use correct loop bounds */
    product := alpha;
    var i := 1;
    
    power1(alpha);
    
    while i < n
        invariant 1 <= i <= n
        invariant product == power(i as real, alpha)
    {
        /* code modified by LLM (iteration 1): Apply powerLemma to establish the relationship for the next iteration */
        powerLemma(i as real, alpha);
        product := product * alpha;
        i := i + 1;
    }
}